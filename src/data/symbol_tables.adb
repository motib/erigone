-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Strings.Fixed;
with Automata.Display, Config, Compiler_Declarations, Execute.Statement;
with Options, State_Vectors, Utilities;
package body Symbol_Tables is

  -- The symbol table
  Symbol_Table: array(Config.Symbol_Index) of Symbol;

  -- The number table is a table of the constant numbers
  Number_Table: array(Byte) of Integer;
  Numbers: Byte;

  -- The string table is a table of the constant strings
  String_Table:  array(Byte) of Line;
  String_Length: array(Byte) of Byte;
  Strings: Byte;

  -- The MType table is a table of names of values
  MType_Table:  array(Byte) of Name;
  MType_Length: array(Byte) of Byte;
  MTypes: Byte;

  -- The channel table. NOTE: the index starts at 1 not 0 !!
  Channel_Table:  array(Config.Channel_Index) of Channel;

  procedure Initialize is
  begin
    Variables   := 0;
    Numbers     := 0;
    Number_Table := (others => Integer'First);
    Strings     := 0;
    MTypes      := 0;
    Channels    := 0;
    Frame_Starts(0) := 0;
    Last_Frame      := 1;
  end Initialize;

  -- Get and set numbers, strings, mtypes, channels, symbols
  function Get_Number(I: Byte) return Integer is
  begin
    return Number_Table(I);
  end Get_Number;

  function Get_String(I: Byte) return String is
  begin
    return String_Table(I)(1..Integer(String_Length(I)));
  end Get_String;

  function Get_MType(I: Byte) return String is
  begin
    return MType_Table(I)(1..Integer(MType_Length(I)));
  end Get_MType;

  function  Get_Channel(I: Byte) return Channel is
  begin
    return Channel_Table(I);
  end Get_Channel;

  function  Get_Symbol(I: Byte) return Symbol is
  begin
    return Symbol_Table(I);
  end Get_Symbol;

  procedure Set_Number(S: in String) is
    Offset: Byte := Utilities.Extract(S, "offset");
    Value:  Integer := Utilities.Extract(S, "value"); 
  begin
    if Number_Table(Offset) = Integer'First then
      Number_Table(Offset) := Value;
      Numbers := Numbers + 1;
    end if;
  end Set_Number;

  procedure Set_String(S: in String) is
    use Utilities;
    S1: String := Extract_Paren(S, "value", """", """");
    I:  Byte   := Extract(S, "offset");
  begin
    String_Table(I)  := Pad(S1, Count=>Line'Length);
    String_Length(I) := S1'Length;
    Strings := Strings + 1;
  end Set_String;

  procedure Set_MType(S: in String) is
    use Utilities;
    S1: String := Trim(Extract(S, "name"));
    I:  Byte   := Extract(S, "value");
  begin
    MType_Table(I)  := Pad(S1);
    MType_Length(I) := S1'Length;
    MTypes := MTypes + 1;
  end Set_MType;

  -- Extract channel declarations
  -- Each message can have a sequence of types/sizes
  procedure Set_Channel(S: in String) is
    use Utilities;
    Ch:     Channel;
    Types:  String := Extract_Paren(S, "element_type");
    Sizes:  String := Extract_Paren(S, "element_size");
    Start:  Positive;   -- For indexing individual elements
    Stop:   Natural;
    Count:  Byte := 0;  -- Count of types and sizes
    Channel_Index: Byte := Byte'Value(Extract(S, "name"));
  begin
    -- Extract from type1,type2,...
    Start := Types'First;
    loop
      Stop := Ada.Strings.Fixed.Index(Types, ",", Start);
      exit when Stop = 0;
      Ch.Element_Types(Count) := Symbol_Type'Value(Types(Start .. Stop-1));
      Start := Stop + 1;
      Count := Count + 1;
      if Count > Config.Message_Index'Last then
        raise Unexpected_Input with "too many elements in channel";
      end if;
    end loop;

    -- Extract from size1,size2,...
    Start := Sizes'First;
    Count := 0;
    Ch.Message_Length := 0;
    loop
      Stop := Ada.Strings.Fixed.Index(Sizes, ",", Start);
      exit when Stop = 0;
      Ch.Element_Sizes(Count) := Byte'Value(Sizes(Start .. Stop-1));
      Ch.Message_Length := Ch.Message_Length + Ch.Element_Sizes(Count); 
      Start := Stop + 1;
      Count := Count + 1;
    end loop;

    Ch.Elements    := Count;
    Ch.Buffer_Size := Extract(S, "buffer_size");
    Ch.Offset      := Extract(S, "offset");
    Ch.Length      := Extract(S, "length");

    -- Store channel (index starts at 1)
    Channels := Channels + 1;
    Channel_Table(Channel_Index) := Ch;
  end Set_Channel;

  -- Extract symbol state from string S and store in Symbol Table
  procedure Set_Symbol(S: in String) is
    Sym: Symbol;
    B:   Automata.Byte_Code_Array;
    use Utilities;
  begin
    Sym.Identifier := Extract(S, "name");
    Sym.Typ        := Symbol_Type'Value(Extract(S, "type"));
    Sym.Parameter  := Extract(S, "parameter");
    Sym.Offset     := Extract(S, "offset");
    Sym.Length     := Extract(S, "length");
    Sym.Size       := Extract(S, "size");
    Sym.Scope      := Extract(S, "scope");
    Automata.Extract_Byte_Code(
      Extract_Paren(S, "byte code"), Sym.Code_Size, B);
    Sym.Byte_Code := new Automata.Byte_Code_Array'(B);
    if Sym.Typ = Array_Type then
      Sym.Element_Typ := Symbol_Type'Value(Extract(S, "element_type"));
    end if;
    Symbol_Table(Variables) := Sym;
    Variables := Variables + 1;
  end Set_Symbol;

  -- The size of the globals is the offset of the first local frame
  procedure Set_Global (S: in String) is
  begin
    Frame_Starts(1) := Utilities.Extract(S, "global_variables");
  end Set_Global;

  -- Each proctype gives the size of the local variables
  procedure Set_Local (B: Byte) is
  begin
    Frame_Starts(Last_Frame + 1) := Frame_Starts(Last_Frame) + B;
    Last_Frame := Last_Frame + 1;
  end Set_Local;

  -- Get total size of data to check size of state vector
  function Get_Data_Size return Byte is
    B: Byte := 0;
  begin
    -- Data needed for variables
    if Variables > 0 then
      for V in 0 .. Variables-1 loop
        B := B + Symbol_Table(V).Length * Symbol_Table(V).Size;
      end loop;
    end if;

    -- Data needed for channels
    for C in 1 .. Channels loop
      B := B + Channel_Table(C).Length;
    end loop;
    return B;
  end Get_Data_Size;

  -- Return an array of initial values of the global variables
  --   by evaluating each initial expression.
  function  Get_Variable_Initials return Byte_Array_Base is
    Result: Integer;   -- Dummy variable for calling Evaluate
    Scratch: State_Vectors.State_Vector;
                       -- Temporary vector for initial values
  begin
    if Variables = 0 then return Scratch.Variable; end if;
    for V in 0 .. Variables-1 loop
      declare
        Sym: Symbol renames Symbol_Table(V);
      begin
        if Sym.Scope = 0 and then Sym.Code_Size /= 0 then
          Execute.Statement.Evaluate(
            Scratch, Sym.Code_Size, Sym.Byte_Code, 0, 0, Result);
  
          -- For arrays, the initial value will be set in the first element
          --   Next, set all elements to the same initial value
          -- Except for channel initializers, which must be replicated
          if Sym.Typ = Array_Type and then Sym.Length > 1 then
            declare
              Initial: Byte_Array_Base :=
                State_Vectors.Get_Variable_Value(
                  Scratch, Sym.Offset, Sym.Size);
            begin
              for E in 1..Sym.Length-1 loop
                if Sym.Element_Typ = Chan_Type then
                  Initial(Initial'First) := Initial(Initial'First) + 1;
                end if;
                State_Vectors.Update_Variable(
                  Scratch, Sym.Offset + E * Sym.Size, Initial);
              end loop;
            end;
          end if;
        end if;
      end;
    end loop;
    return Scratch.Variable;
  end Get_Variable_Initials;

  -- Display the frame table
  --   Called also after a "run" instruction
  procedure Put_Frame_Table is
    use Ada.Text_IO, Utilities;
  begin  
    Put_Line("frame table start=,");
        Put("global=,");
        Put("offset=", Frame_Starts(0), New_Line => True);
    for V in 0 .. Automata.Processes-1 loop
      if Automata.Program(V).Is_Active then
        Put("pid=", Automata.Program(V).PID);
        Put("offset=", Frame_Starts(V+1), New_Line => True);
      end if;
    end loop;
    Put_Line("frame table end=,");
  end Put_Frame_Table;
  
  -- Display the symbol table, the number table and the string table
  procedure Put_Symbol_Table is
    use Ada.Text_IO, Utilities;

    -- Put one symbol
    procedure Put_Symbol(V: in Config.Symbol_Index) is
      S: Symbol renames Symbol_Table(V);
    begin
      Put("name="   & Utilities.Trim(S.Identifier)); 
      Put(",type="  & Utilities.To_Lower(Symbol_Type'Image(S.Typ)));
  
      if S.Typ = Array_Type then
        Put(",element_type="  & 
            Utilities.To_Lower(Symbol_Type'Image(S.Element_Typ)));
      end if;
  
      Utilities.Put(",offset=",   S.Offset);
      Utilities.Put("length=",    S.Length);
      Utilities.Put("size=",      S.Size);
      Utilities.Put("scope=",     S.Scope);
      Utilities.Put("parameter=", S.Parameter);
      Automata.Display.Put_Byte_Code(S.Code_Size, S.Byte_Code);
    end Put_Symbol;
  
    -- Put a channel
    procedure Put_Channel(Ch: Channel) is
    begin
      Put("buffer_size=", Ch.Buffer_Size);
      Put("offset=", Ch.Offset);
      Put("length=", Ch.Length);
      Put("message_length=", Ch.Message_Length);
      Put("elements=", Ch.Elements);
      Put("element type={");
      for E in 0 .. Ch.Elements-1 loop
        Put(To_Lower(Symbol_Type'Image(Ch.Element_Types(E))) & ",");
      end loop;
      Put("}");
      Put(",element size={");
      for E in 0 .. Ch.Elements-1 loop
        Put("", Ch.Element_Sizes(E));
      end loop;
      Put_Line("},");
    end Put_Channel;

  begin
    if not Options.Display(Options.Program) then return; end if;

    -- Display the symbol table
    if Variables > 0 then
      Put_Line("symbol table start=,");
      Put("variables=", Variables, New_Line => True);
      for V in 0 .. Variables-1 loop
        Put_Symbol(V);
      end loop;
      Put_Line("symbol table end=,");
    end if;

    -- Display the number table
    if Numbers > 0 then
      Put_Line("number table start=,");
      Put("numbers=", Numbers, New_Line => True);
      for I in 0 .. Numbers-1 loop
        Put("offset=", I);
        Put("value=",  Number_Table(I), New_Line => True);
      end loop;
      Put_Line("number table end=,");
    end if;

    -- Display the string table
    if Strings > 0 then
      Put_Line("string table start=,");
      Put("strings=", Strings, New_Line => True);
      for I in 0 .. Strings-1 loop
        Put("offset=", I);
        Put_Line("value=""" & 
                 String_Table(I)(1..Integer(String_Length(I))) & """,");
      end loop;
      Put_Line("string table end=,");
    end if;

    -- Display the mtype table
    if MTypes > 0 then
      Put_Line("mtype table start=,");
      Put("mtypes=", MTypes, New_Line => True);
      for I in 1 .. MTypes loop
        Put("offset=", I);
        Put_Line("value=""" & 
                 MType_Table(I)(1..Integer(MType_Length(I))) & """,");
      end loop;
      Put_Line("mtype table end=,");
    end if;

    -- Display the channel table
    if Channels > 0 then
      Put_Line("channel table start=,");
      Put("channels=", Channels, New_Line => True);
      for I in 1 .. Channels loop
        Put("index=", I);
        Put_Channel(Channel_Table(I));
      end loop;
      Put_Line("channel table end=,");
    end if;

    Put_Frame_Table;

    Put("data size=", Get_Data_Size, New_Line => True);
  end Put_Symbol_Table;
end Symbol_Tables;
