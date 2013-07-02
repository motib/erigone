-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO, Compiler_Declarations;
with Compiler_Global, Expr, Lexer, Preprocess, State, Util;
use  Ada.Text_IO, Compiler_Declarations, Compiler_Global, Lexer, Util;
package body Compile is
  Channel_Counter: Integer;   -- Number of channel initializers
  MType_Code:      Integer;
  Number_Iterator: Integer;

  -- Compile "mtype = {...};" declaration
  --   Enter names into symbol table and assign codes in reverse order
  procedure MType_Declaration is
    T0:   Integer := T+1;   -- Start index to assign in reverse order
  begin
    In_Symbol;
    if Sy = becomes_sy then In_Symbol; end if;
    Check_Symbol(lbrace_sy,  "{");
    -- Enter each mtype name
    while Next_Sy = comma_sy or Next_Sy = rbrace_sy loop
      Enter(Id, MType);
      In_Symbol;
      In_Symbol;
    end loop;
    -- Assign values and put mtype line to output file
    for T1 in reverse T0..T loop
      Tab(T1).Adr := MType_Code;
      Put_Line(Aut, "mtype=,name=" & Trim(Tab(T1).Name) &
                    ",value="      & Trim_Int(MType_Code) & ",");
      MType_Code := MType_Code + 1;
    end loop;
    Check_Symbol(semicolon_sy, ";");
  end MType_Declaration;

  -- Compile channel initialization "= [N] of {type,type,...}"
  procedure Channel_Declaration is
    Size:    Field_Array_Type;   -- Array of element sizes
    Types:   array (Field_Index) of Symbol;
    Count:   Integer := 0;       -- Number of message entries
    Offset0: Integer;            -- Initial offset to compute length
  begin
    Check_Symbol(lbracket_sy, "[");
    Check_Symbol(intcon_sy,   "integer");
    Check_Symbol(rbracket_sy, "]");
    Check_Symbol(of_sy,       "of");
    Check_Symbol(lbrace_sy,   "{");
    while Type_Begin_Sy(sy) loop
      case Sy is
        when byte_sy | bool_sy | bit_sy | mtype_sy | chan_sy =>
          Size(Count)  := 1;
        when short_sy => Size(Count) := 2;
        when int_sy   => Size(Count) := 4;
        when others   => null;
      end case;
      Types(Count) := Sy;
      Count := Count + 1;
      In_Symbol;
      if sy = comma_sy then
        In_Symbol;
      elsif sy = rbrace_sy then
        In_Symbol;
        exit;
      else
        Error("comma or right brace expected");
      end if;
    end loop;

    -- Put channel data to aut file; it may be an array
    for A in 1 .. Tab(T).Len loop
      Channel_Counter := Channel_Counter + 1;
      Put(Aut, "channel=,name=" & Trim_Int(Channel_Counter) &
               ",buffer_size="  & Trim_Int(Inum)       &
               ",offset="       & Trim_Int(Offset));
      Put(Aut, ",element_type={");
      for C in 0 .. Count-1 loop
        case Types(C) is
          when bit_sy  | bool_sy => Put(Aut, "bit_type,");
          when byte_sy | chan_sy => Put(Aut, "byte_type,");
          when mtype_sy          => Put(Aut, "mtype_type,");
          when short_sy          => Put(Aut, "short_type,");
          when int_sy            => Put(Aut, "int_type,");
          when others => null;
        end case;
      end loop;
      Offset0 := Offset;
      -- Put the list of the element sizes and the total length
      -- Add a byte for the current number of elements
      Offset := Offset + 1;
      -- For a rendezvous channel, add a single message to the state vector
      if Inum = 0 then Inum := 1; end if;
      Put(Aut, "},element_size={");
      for S in 0..Count-1 loop
        Put(Aut, Trim_Int(Size(S)) & ",");
        Offset := Offset + Inum*Size(S);
      end loop;
      Put_Line(Aut, "},length=" & Trim_Int(Offset-Offset0) & ",");
    end loop;
  end Channel_Declaration;

  -- Compile variable declaration
  --   For parameters, the initialization is different
  procedure Variable_Declaration(Is_Parm: Boolean := False) is
    T0, T1, Sz, Len, Save_CC, Lv: Integer;
    Tp, Et , El_Typ: Types;
  begin
    Et := No_Typ;
    case Sy is
      when Bit_Sy  | Bool_Sy    => Tp := Bits;   Sz := 1;
      when Byte_Sy | pid_typ_Sy => Tp := Bytes;  Sz := 1;
      when short_sy             => Tp := Shorts; Sz := 2;
      when int_sy               => Tp := Ints;   Sz := 4;
      when MType_Sy             => Tp := MTypes; Sz := 1;
      when Chan_Sy              => Tp := Chans;  Sz := 1;
      when others               => null;
    end case;
    El_Typ := Tp;

    -- Read each identifier
    In_Symbol;
    T0  := T;
    while Sy = Ident_Sy loop
      Len := 1;
      if Is_Parm then Enter(Id, Parameter);
      else            Enter(Id, Variable);
      end if;
      In_Symbol;

      -- Left bracket means an array
      if Sy = Lbracket_Sy then
        Tp := Arrays;
        In_Symbol;
        Check_Symbol(intcon_sy, "integer");
        Len := Inum;
        Check_Symbol(Rbracket_Sy, "]");
      elsif Tp = Arrays then  -- For "byte a[3], b"
        Tp := El_Typ;
      end if;

      -- The declaration can have many variables: "byte a,b,c"
      T1 := T;
      while T0 < T1 loop
        T0             := T0 + 1;
        Tab(T0).Eltype := El_Typ;
        Tab(T0).Typ    := Tp;
        Tab(T0).Lev    := Level;
        Tab(T0).Adr    := Offset;
        Tab(T0).Len    := Len;
        Tab(T0).Sz     := Sz;
        Offset         := Offset + Sz * Len;

        -- Initialization of a variable or a channel initializer
        if Sy = Becomes_Sy then
          In_Symbol;
          if Sy = Lbracket_Sy then
            -- Initialize variable with first channel
            Save_CC := Channel_Counter;
            Channel_Declaration;
            Emit(byte_push, Save_CC+1, 0);
            Emit(Byte_Store, Tab(T0).Adr, 0);
          else
            if Level > 0 then
              State.Init_Transition (State_Number, State_Number + 1);
            end if;
            Expr.Expression;
            if Level > 0 then Lv := 1; else Lv := 0; end if;
            case Tp is
              when Ints   => Emit(Int_Store,   Tab(T0).Adr, Lv);
              when Shorts => Emit(Short_Store, Tab(T0).Adr, Lv);
              when others => Emit(Byte_Store,  Tab(T0).Adr, Lv);
            end case;
            if Level > 0 then
              Increment_Transition_Counter;
              State_Number  := State_Number + 1;
            end if;
          end if;
        end if;

        -- If more than one variable, there will be a comma
        if Sy = Comma_Sy then In_Symbol; end if;
      end loop;
    end loop;
    if not Is_Parm then Check_Symbol(semicolon_sy, "}"); end if;
  end Variable_Declaration;

  -- If some transition has a target after all transitions,
  --   add a transition with end=1 and the halt byte code
  procedure Add_Halt_Transition is
  begin
    for I in 0..Transition_Counter-1 loop
      if T_Tab(I).Target = State_Number then
        T_Tab(Transition_Counter) :=
         (Source       => State_Number,
          End_Label    => 1,
          Statement    => new String'(""),
          Code_Size    => 1,
          Byte_Code    => new Byte_Code_Array'(
                            0 => (halt,0,0), others => (noop,0,0)),
          others       => <>);
        Increment_Transition_Counter;
        exit;
      end if;
    end loop;
  end Add_Halt_Transition;

  -- Remove noops by directing incoming transitions to its target
  procedure Remove_Noops is
    Changed:     Boolean := True;
    Noop_Source: Integer;
    Noop_Target: Integer;
  begin
    while Changed loop
      Changed := False;
      for I in 0..Transition_Counter-1 loop
        if T_Tab(I).Code_Size = 1 and T_Tab(I).Byte_Code(0).Operator = noop then
          Noop_Source := T_Tab(I).Source;
          Noop_Target := T_Tab(I).Target;
          for J in 0..Transition_Counter-1 loop
            if T_Tab(J).Target = Noop_Source then
              -- Redirect target from noop transitions to noop's target
              T_Tab(J).Target := Noop_Target;
              Changed := False;
            end if;
          end loop;
          -- Remove noop transition
          T_Tab(I .. Transition_Counter-2) :=
            T_Tab(I+1 .. Transition_Counter-1);
          Transition_Counter := Transition_Counter-1;
        end if;
      end loop;
    end loop;
  end Remove_Noops;

  -- Compile a process declaration
  --   Active=0 for "proctye"
  --   Active=1 for "active proctype"
  --   Active=N for "active[N] proctype"
  --   Is_Init is true if "init"
  procedure Process_Declaration is
    Is_Init : Boolean := False;
    Active  : Integer := 0;

    -- After "active" is seen, process "[N]", if any 
    procedure Set_Active is
    begin
      In_Symbol;
      Active := 1;
      if Sy = LBracket_sy then
        In_Symbol;
        if Sy = IntCon_sy then
          Active := Inum;
          In_Symbol;
          Check_Symbol(rbracket_sy, "]");
        else 
          Error("integer expected");
        end if;
      end if;
    end Set_Active;

  begin  -- Process declaration
    Transition_Counter := 0;
    State_Number  := 1;
    Offset := 0;

    -- Check for "init" process"
    if Sy = Init_Sy then
      In_Symbol;
      Is_Init := True;
      Id      := Pad("init");
      Active  := 1;
    else
      if Sy = Active_Sy then Set_Active; end if;
      Check_Symbol(proctype_sy, "proctype");
      Check_Symbol(ident_sy,    "identifer");
    end if;

    -- Enter proctype in symbol table
    Enter (Id, Process);
    Tab(T).Lev     := 0;               -- proctypes are global
    Tab(T).Len     := 0;               -- number of parameters
    Process_Number := Process_Number + 1;
    Tab(T).Adr     := Process_Number;  -- For "run" instruction
    Level          := T;               -- Index of process name

    -- For each parameter, store its symbol table index in the
    --   Parms field of the symbol table entry for the proctype
    if not Is_Init then
      Check_Symbol(lparent_sy, "(");
      while Type_Begin_Sy(Sy) loop
        Variable_Declaration(Is_Parm => True);
        Tab(Level).Parms(Tab(Level).Len) := T;
        Tab(Level).Len := Tab(Level).Len + 1;
        if Sy = semicolon_sy then In_Symbol; end if;
      end loop;
      Check_Symbol(rparent_sy, ")");
    end if;

    -- Compile local declarations
    -- Emit initialization code to the symbol table
    Check_Symbol(lbrace_sy, "{");
    while Type_Begin_Sy (Sy) loop
      -- Ignore xr and xs definitions
      if Sy = xr_sy or Sy = xs_sy then
        loop In_Symbol; exit when Sy = semicolon_sy; end loop;
        In_Symbol;
      else
        Variable_Declaration;
      end if;
    end loop;

    -- Compile statements
    while Statement_Begin_Sy (Sy) or Factor_Begin_Sy (Sy) or Type_Begin_Sy (Sy) loop
      if Type_Begin_Sy (Sy) then
        Variable_Declaration;
      else
        State.Statement;
      end if;
    end loop;
    Check_Symbol(rbrace_sy, "}");

    Add_Halt_Transition;  -- Add halt transition if needed
    State.Fix_Gotos;      -- Fix up goto statements
    Remove_Noops;         -- Remove noops introduced for if-statements

    -- Put transitions and symbols for this proctype
    Put_Line(Aut, "process="      & Trim (Tab(Level).Name) &
                  ",active="      & Trim_Int(Active)    &
                  ",initial=1,"   &
                  "transitions="  & Trim_Int(Transition_Counter) & "," &
                  "local_variables=" & Trim_Int(Offset) & ",");
    Put_Transitions;
    Put_Symbols;
  end Process_Declaration;

  -- Compile an expression from an LTL formula
  function Compile_Expression(E: String) return String is
    S: String(1..1024);   -- Build the string of byte codes here
    I: Integer := 1;     -- Count of the characters used in the string S
    Index: Natural;
    Last_Token: Natural := Token_Counter;
  begin
    -- Initialize the Lexer, but not the symbol table, etc.
    Lexer.Initialize(E);
    No_File := True;           -- Tell the lexer not to read lines

    -- Arbitrarily emit the byte code into the first transition
    Transition_Counter := 0;
    T_Tab(0).Code_Size := 0;

      Get_Symbol;
      Get_Symbol;  -- Because of Next_Sy
      while Sy /= eof_sy loop
        if    Sy = ident_sy  then Index := IDNum;
        elsif Sy = intcon_sy then Index := INum;
        elsif Sy = strng_sy  then Index := Str;
        else  Index := 0;
        end if;
        Token_Tab(Token_Counter) :=
          (Sy, Index, Lexer.Get_Line_Counter, Lexer.Get_Buffer_Ptr);
        Token_Counter := Token_Counter + 1;
        Get_Symbol;
      end loop;
    Preprocess.Use_Inline(Is_Define => True, Start_From => Last_Token); 
    In_Symbol;
    In_Symbol;
    Expr.Expression;
    Number_Iterator := Number_Counter;
    
    -- Format the byte code to the returned string
    for B in 0 .. T_Tab(0).Code_Size-1 loop
      declare
        BC: String := Format_Code(T_Tab(0).Byte_Code(B));
      begin
        S(I .. I+BC'Length-1) := BC;
        I := I + BC'Length;
      end;
    end loop;
    return S(1..I-1);
  end Compile_Expression;

  -- Get numbers after compiling LTL which might have a constant
  function Get_I_Tab return String is
  begin
    if Number_Iterator = 0 then
      return "";
    else
      Number_Iterator := Number_Iterator - 1;
      return "offset=" & Integer'Image(Number_Iterator) &
             ",value=" & Integer'Image(I_Tab(Number_Iterator)) & ",";
    end if;
  end Get_I_Tab;
  
  procedure Init_Compiler is
  begin
    -- Initialization of other packages
    Lexer.Initialize("");

    -- Initialization of global variables and flags
    Level             := 0;
    Offset            := 0;
    Process_Number    := 0;
    T                 := 0;
    MType_Code        := 1;

    Number_Counter    := 0;
    String_Counter    := 0;
    Channel_Counter   := 0;
    ID_Counter        := 0;
    Token_Counter     := 0;

    Declaration       := False;
    Emit_Load_Address := False;
    Is_Copy           := False;
    LHS_Array         := False;
    No_File           := False;

    Tab(T)            := (others => <>);
    State.Initialize;
  end Init_Compiler;

  -- Compile a Promela program from the Input_File
  procedure Compile_File(
    Source_File_Name: in String; Automata_File_Name: in String) is
  begin
    begin
      Open  (Inp, In_File,  Source_File_Name);
    exception
      when others => raise File_Error
        with "cannot open file """ & Source_File_Name & """";
    end;
    begin
      Create(Aut, Out_File, Automata_File_Name);
    exception
      when others => raise File_Error
        with "cannot create file """ & Automata_File_Name & """";
    end;

    Init_Compiler;
    Preprocess.Preprocess_File;
    Close(Inp);
    Tok := 0;
    
    In_Symbol;
    In_Symbol;  -- Because of Next_Sy

    -- Global declarations
    Declaration := True;    -- Emit initialization code to symbol table
    while Type_Begin_Sy (Sy) loop
      -- mtype = {...} declaration
      if Sy = mtype_sy and
         (Next_Sy = becomes_sy or Next_Sy = lbrace_sy) then
        MType_Declaration;
      elsif Sy = hidden_Sy or Sy = local_sy then
        In_Symbol;
      else
        Variable_Declaration;
      end if;
    end loop;
    Declaration := False;
    Put_Symbols;
    Put_Line(Aut, "global_variables=" & Trim_Int(Offset) & ",");

    if not Process_Begin_Sy(Sy) then
      Error("variable or process declaration expected");
    end if;

    -- Processes
    while Process_Begin_Sy(Sy) loop
      Process_Declaration;
    end loop;

    Put_Numbers;
    Put_Strings;
    Close(Aut);
  end Compile_File;
end Compile;
