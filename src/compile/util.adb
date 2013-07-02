-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Characters.Handling, Ada.Strings.Fixed;
with Ada.Text_IO, Compiler_Global, Lexer;
use  Ada.Text_IO, Compiler_Global;
package body Util is
  -- Check if the capacity of a table has been exceeded
  procedure Check_Table(Value, Max: Integer; Name: String) is
  begin
    if Value > Max then
      raise Compiler_Declarations.Compilation_Error
        with Name & " table too small (" & Trim_Int(Max+1) & ")";
    end if;
  end Check_Table;

  -- Call Integer'Image and then Trim to remove the leading blank
  function Trim_Int(N: Integer) return String is
  begin
    return Trim(Integer'Image(N));
  end Trim_Int;

  procedure Put_Numbers is
  begin
    for N in 0 .. Number_Counter - 1 loop
      Put_Line(Aut, "number=,offset=" & Trim_Int(N) &
                    ",value="         & Trim_Int(I_Tab(N)) & ",");
    end loop;
  end Put_Numbers;

  procedure Put_Strings is
  begin
    for N in 0 .. String_Counter - 1 loop
      Put_Line(Aut, "string=,offset=" & Trim_Int(N) &
                    ",value="""       & S_Tab(N).all & """,");
    end loop;
  end Put_Strings;

  procedure Put_Symbols is
  begin
    for I in 1 .. T loop
      -- Put only variables of the current level
      if (Tab(I).Obj = Variable or Tab(I).Obj = Parameter) and 
          Tab(I).Lev = Level then
        Put(Aut, "symbol=,type=");
        case Tab(I).Typ is
          when Bits            => Put(Aut, "bit_type");
          when Bytes  | Mtypes => Put(Aut, "byte_type");
          when Shorts          => Put(Aut, "short_type");
          when Ints            => Put(Aut, "int_type");
          when Chans           => Put(Aut, "chan_type");
          when Arrays          =>
            Put(Aut, "array_type,element_type=");
            case Tab(I).ElType is
              when Bits            => Put(Aut, "bit_type");
              when Bytes  | Mtypes => Put(Aut, "byte_type");
              when Shorts          => Put(Aut, "short_type");
              when Ints            => Put(Aut, "int_type");
              when Chans           => Put(Aut, "chan_type");
              when others          => null;
            end case;
          when others                => null;
        end case;

        -- For local variable, prefix with process name
        Put(Aut, ",name=");
        if Tab(I).Lev /= 0 then
          Put(Aut, Trim(Tab(Tab(I).Lev).Name) & ".");
        end if;
        Put(Aut,
            Trim(Tab(I).Name)  &
            ",offset="         & Trim_Int(Tab(I).Adr) & 
            ",length="         & Trim_Int(Tab(I).Len) &
            ",size="           & Trim_Int(Tab(I).Sz));

        if Tab(I).Obj = Parameter then Put(Aut, ",parameter=1");
        else                           Put(Aut, ",parameter=0");
        end if;

        if Tab(I).Lev = 0 then Put(Aut, ",scope=0");
        else                   Put(Aut, ",scope=1");
        end if;

        -- Put the byte code for the initialization
        Put(Aut, ",byte code={");
        for D in 0 .. Tab(I).Code_Size - 1 loop
          Put_Byte_Code (Tab(I).Byte_Code (D));
        end loop;
        Put_Line(Aut, "},");
      end if;
    end loop;
  end Put_Symbols;

  procedure Put_Transitions is
    Stmt : Lines;    -- For formatting the statement
    I    : Integer;  -- Index within Stmt
    use Ada.Strings.Fixed;
  begin
    for C in 0 .. Transition_Counter - 1 loop
      -- Print statement without: ":: ", trailing ";", "->", "{"
      Stmt := Pad(T_Tab(C).Statement.all, Lines'Length);
      I := Index(Stmt, "::");
      if I /= 0 then Delete(Stmt, I, I+1); end if;

      Stmt := Pad(Trim(Stmt), Lines'Length);
      I := Index_Non_Blank(Stmt, Going => Ada.Strings.Backward);
      if I /= 0 and then Stmt(I) = ';' then Stmt(I) := ' '; end if;

      I := Index_Non_Blank(Stmt, Going => Ada.Strings.Backward);
      if I > 1 and then Stmt(I-1..I) = "->" then
        Delete(Stmt, I-1, I);
      end if;

      I := Index_Non_Blank(Stmt, Going => Ada.Strings.Backward);
      if I /= 0 and then Stmt(I) = '{' then Stmt(I) := ' '; end if;

      Put(Aut,
          "number="      & Trim_Int(C) &
          ",source="     & Trim_Int(T_Tab(C).Source) &
          ",target="     & Trim_Int(T_Tab(C).Target) &
          ",atomic="     & Trim_Int(T_Tab(C).Atomic) &
          ",end="        & Trim_Int(T_Tab(C).End_Label) &
          ",accept="     & Trim_Int(T_Tab(C).Accept_Label) &
          ",line="       & Trim_Int(T_Tab(C).Line_Number) &
          ",statement={" & Trim(Stmt) &
          "},byte code={");
      for D in 0 .. T_Tab(C).Code_Size - 1 loop
        Put_Byte_Code(T_Tab(C).Byte_Code(D));
      end loop;
      Put_Line(Aut, "},");
    end loop;
  end Put_Transitions;

  -- Format a byte code
  function Format_Code (B : in Byte_Code) return String is
  begin
    return
        Ada.Characters.Handling.To_Lower(
        Compiler_Declarations.Opcode'Image (B.Operator)) &
        Integer'Image (B.Operand1) &
        Integer'Image (B.Operand2) & ",";
  end Format_Code;

  -- Format and put a byte code
  procedure Put_Byte_Code (B : in Byte_Code) is
  begin
    Put(Aut, Format_Code(B));
  end Put_Byte_Code;

  -- Increment Transition_Counter, checking for table overflow
  procedure Increment_Transition_Counter is
  begin
    Transition_Counter := Transition_Counter + 1;
    Check_Table(Transition_Counter, Transition_Index'Last, "transition");
  end Increment_Transition_Counter;

  -- Enter an identifer into the symbol table
  procedure Enter (Id : in Alfa; K : in Objects) is
  begin
    T := T + 1;
    Check_Table(T, Tab'Last, "symbol");
    Tab(T) := (Name => Id, Obj => K, Lev => Level,
               Byte_Code => new Byte_Code_Array'(others => <>),
               others => <>);
  end Enter;

  -- Search for an identifier in the symbol table
  --   Return index or zero if not found
  function Loc(Id : Alfa) return Integer is
    J : Integer := T;
  begin
    Tab(0).Name := Id;   -- Sentinel
    Tab(0).Lev  := 0;
    -- Identifier must be global or local to the same proctype
    while (Tab(J).Name /= Id) or else
          ((Tab(J).Lev /= 0) and (Tab(J).Lev /= Level)) loop
      J := J - 1;
    end loop;
    return J;
  end Loc;

  -- Emit a byte code into the byte code table
  --   of the current symbol or transition
  procedure Emit(
    Fct : in Compiler_Declarations.Opcode; A, B : in Integer) is
    use Compiler_Declarations;
  begin
    if Declaration then  -- compiling global variable
      Check_Table(Tab(T).Code_Size, Byte_Code_Index'Last, "byte code");
      Tab(T).Byte_Code(Tab(T).Code_Size) := (Fct, A, B);
      Tab(T).Code_Size := Tab(T).Code_Size + 1;
    else                 -- compiling transition
      Check_Table(T_Tab(Transition_Counter).Code_Size, 
        Byte_Code_Index'Last, "byte code");
      T_Tab(Transition_Counter).Byte_Code(
        T_Tab(Transition_Counter).Code_Size) := (Fct, A, B);
      T_Tab(Transition_Counter).Code_Size    :=
        T_Tab (Transition_Counter).Code_Size + 1;
    end if;
  end Emit;
end Util;
