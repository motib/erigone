-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO, Ada.Strings.Fixed;
with Automata, Options, Symbol_Tables, Utilities;
package body State_Vectors is
  -- Get initial values for state vector
  function Get_Initial_State_Vector return State_Vector is
    S: State_Vector;
  begin
    S.Process  := Automata.Get_Process_Initials(Config.Process_Index);
    S.Variable := Symbol_Tables.Get_Variable_Initials(Config.Data_Index);
    return S;
  end Get_Initial_State_Vector;

  -- Return the value of the location counter of Process from state vector S
  function Get_Process_Location_Value(
    S: State_Vector; Process: Byte) return Byte is
  begin
    return S.Process(Process);
  end Get_Process_Location_Value;

  -- Update the Value of a location counter in a Process in state vector S
  --   Procedures for single-byte values and for multiple-byte values
  procedure Update_Process_Location(
    S:       in out State_Vector; 
    Process: in Byte; 
    Value:   in Byte) is
  begin
    S.Process(Process) := Value;
  end Update_Process_Location;

  -- Return the value of a Variable from state vector S
  --   Functions for bytes, shorts and ints
  function Get_Byte_Variable_Value(
    S: State_Vector; Addr:    Byte) return Byte is
  begin
    return S.Variable(Addr);
  end Get_Byte_Variable_Value;

  function Get_Short_Variable_Value(
      S: State_Vector; Addr:    Byte) return Integer is
      Sign: Byte := 0;
  begin
    if S.Variable(Addr+1) >= 128 then Sign := 255; end if;
    return Bytes_To_Integer(
      Four_Bytes'(S.Variable(Addr), S.Variable(Addr+1), Sign, Sign)); 
  end Get_Short_Variable_Value;

  function Get_Int_Variable_Value(
    S:       State_Vector; Addr:    Byte) return Integer is
  begin
    return Bytes_To_Integer(S.Variable(Addr .. Addr + 3));
  end Get_Int_Variable_Value;

  -- Function that calls the appropriate "Get" according to Size
  function Get_Variable_Value_By_Size(
    S:       State_Vector; 
    Addr:    Byte;
    Size:    Byte) return Integer is
  begin
    if Size = 1 then
      return Integer(Get_Byte_Variable_Value(S, Addr));
    elsif Size = 2 then
      return Get_Short_Variable_Value(S, Addr);
    elsif Size = 4 then
      return Get_Int_Variable_Value(S, Addr);
    end if;
    return 0;  -- Dummy to avoid compiler warning
  end Get_Variable_Value_By_Size;

  -- Get multiple bytes with one call 
  function Get_Variable_Value(
    S:       State_Vector;
    Addr:    Byte;
    Size:    Byte) return Byte_Array_Base is
  begin
    return S.Variable(Addr .. Addr + Size-1);
  end Get_Variable_Value;

  -- Update the Value of a Variable in the state vector S
  --   Procedures for bytes, shorts and ints
  procedure Update_Byte_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Byte) is
  begin
    S.Variable(Addr) := Value;
  end Update_Byte_Variable;

  procedure Update_Short_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Integer) is
  begin
    S.Variable(Addr .. Addr + 1) := Integer_To_Bytes(Value)(0..1);
  end Update_Short_Variable;

  procedure Update_Int_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Integer) is
  begin
    S.Variable(Addr .. Addr + 3) := Integer_To_Bytes(Value);
  end Update_Int_Variable;

  -- Procedure that calls the appropriate "Update" according to Size
  procedure Update_Variable_By_Size(
    S:        in out State_Vector;
    Addr:     in Byte;
    Size:     in Byte;
    Value:    in Integer) is
  begin
    if Size = 1 then
      Update_Byte_Variable(S, Addr, Byte'Mod(Value));
    elsif Size = 2 then
      Update_Short_Variable(S, Addr, Value);
    elsif Size = 4 then
      Update_Int_Variable(S, Addr, Value);
    end if;
  end Update_Variable_By_Size;

  -- Update multiple bytes (the Length of the array Value) with one call
  procedure Update_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Byte_Array_Base) is
  begin
    S.Variable(Addr .. Addr + Value'Length-1) := Value;
  end Update_Variable;

  -- Put a prefix string P, followed by the state vector S
  procedure Put_State_Vector(P: in String; S: in State_Vector) is
    use type Options.Execution_Type, Symbol_Tables.Symbol_Type;
    use Utilities, Ada.Text_IO, Ada.Strings.Fixed;
    Sym:    Symbol_Tables.Symbol;
    Ch:     Symbol_Tables.Channel;
    Value, Size, Addr:     Byte;

    -- Put a symbol. Frame is the offset of the process
    procedure Put_One_Symbol(Frame: in Byte) is
      use Symbol_Tables;

      -- The symbol may be an array so this subprogram puts one value
      --   L is the index in the array
      procedure Put_One_Value(T: in Symbol_Type; L: in Byte) is
        Op: Byte := Frame_Starts(Frame) + Sym.Offset + L * Sym.Size;
      begin
        case T is
          when Byte_Type | Bit_Type | Chan_Type =>
            Put(S.Variable(Op));
          when Short_Type =>
            Put(Get_Short_Variable_Value(S, Op));
          when Int_Type =>
            Put(Get_Int_Variable_Value(S, Op));
          when others => null;
        end case;
      end Put_One_Value;

    begin
      Put(Trim(Sym.Identifier));
      case Sym.Typ is
        when MType_Type =>
          Put("=" & Get_MType(S.Variable(Sym.Offset)) & ",");
        when Array_Type =>
          Put("={");
          for L in 0..Sym.Length-1 loop
            Put_One_Value(Sym.Element_Typ, L);
          end loop;
          Put("},");
        when Byte_Type | Bit_Type | Chan_Type | Short_Type | Int_Type =>
          Put("=");
          Put_One_Value(Sym.Typ, 0);
        when others =>
          null;
      end case;
    end Put_One_Symbol;
    
  begin
    -- Put prefix string
    Put(P);

    -- Put values for each global variable
    for I in 0..Symbol_Tables.Variables-1 loop
      Sym := Symbol_Tables.Get_Symbol(I);
      if Sym.Scope = 0 then
        Put_One_Symbol(0);
      end if;
    end loop;

    -- Put the data for each active process
    for I in 0..Automata.Processes-1 loop
      declare
        PT:   Automata.Process_Type renames Automata.Program(I);
        -- Get the process name and if it is P_N, just the P
        Name: String := Trim(PT.Identifier);
        Root: Integer := Name'Length;
      begin
        if PT.Is_Active then
          if Index(Name, "_") /= 0 then
            Root := Index(Name, "_") - 1;
          end if;
          Put(Name & "=", S.Process(I));
          for J in 0..Symbol_Tables.Variables-1 loop
            Sym := Symbol_Tables.Get_Symbol(J);
            if Name(1..Root) = Sym.Identifier(1..Root) then
              Put_One_Symbol(PT.PID+1);
            end if;
          end loop;
        end if;
      end;
    end loop;

    -- Display channels if there are any and if requested
    if Symbol_Tables.Channels /= 0 and then 
       Options.Display(Options.Channels) then
      for I in 1 .. Symbol_Tables.Channels loop
        Ch := Symbol_Tables.Get_Channel(I);
        Put("channel" & Trim(Byte'Image(I)) & "={");
        -- Nothing to display if channel is empty
        -- First byte in channel is the number of messages in it
        if S.Variable(Ch.Offset) /= 0 then
          Put("", S.Variable(Ch.Offset));
          Addr := Ch.Offset + 1;
          -- For each message in the channel
          for C in 0 .. S.Variable(Ch.Offset)-1 loop
            Put("[");
            -- For each element in a message
            for E in 0 .. Ch.Elements-1 loop
              Size := Ch.Element_Sizes(E);
              if Size = 1 then
                Value := S.Variable(Addr);
                if Ch.Element_Types(E) = Symbol_Tables.MType_Type then
                  Put(Symbol_Tables.Get_MType(Value) & ",");
                else
                  Put("", Value);
                end if;
              elsif Size = 2 then
                Put(Get_Short_Variable_Value(S, Addr));
              elsif Size = 4 then
                Put(Get_Int_Variable_Value(S, Addr));
              end if;
              Addr := Addr + Size;
            end loop;
            Put("],");
          end loop;
        end if;
        Put("},");
      end loop;
    end if;

    -- Inner flag displayed if acceptance or fairness verification
    if Options.Execution_Mode = Options.Acceptance or
       Options.Execution_Mode = Options.Fairness   then
      Put("inner=", S.Inner);
    end if;

    -- Fairness counter displayed if fairness verification
    if Options.Execution_Mode = Options.Fairness   then
      Put("fair=", S.Fair);
    end if;

    Put("atomic=", S.Atomic);

    New_Line;
  end Put_State_Vector;
end State_Vectors;
