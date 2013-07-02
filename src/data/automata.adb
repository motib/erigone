-- Copyright 2008-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO, Ada.Strings.Fixed, Ada.Exceptions;
with Automata.Display, Compiler_Declarations, LTL, Config, Files;
with Options, State_Stack, Symbol_Tables, Utilities;
with Ada.Containers.Generic_Array_Sort;
package body Automata is
  PID_Counter: Byte;        -- Counter for assigning PIDs

  procedure Initialize is
  begin
    Processes     := 0;
    Never         := Global.None;
    Accept_Count  := 0;
    PID_Counter   := 0;
  end Initialize;

  -- Redefine "=" because of access types and code size
  function "="(Left, Right: Transitions) return Boolean is
    Equal: Boolean := True;
  begin
    Equal := Equal and Left.Statement.all = Right.Statement.all;
    Equal := Equal and Left.Source        = Right.Source;
    Equal := Equal and Left.Target        = Right.Target;
    Equal := Equal and Left.Atomic        = Right.Atomic;
    Equal := Equal and Left.End_Label     = Right.End_Label;
    Equal := Equal and Left.Accept_Label  = Right.Accept_Label;
    Equal := Equal and Left.Line_Number   = Right.Line_Number;
    Equal := Equal and Left.Code_Size     = Right.Code_Size;
    if Left.Code_Size > 0 then
      for C in 0 .. Left.Code_Size loop
        Equal := Equal and Left.Byte_Code(C) = Right.Byte_Code(C);
      end loop;
    end if;
    return Equal;
  end "=";

  -- < is the lexicographic order used to sort transitions
  --   They are sorted by Source state and then by Target state
  --     except that transitions for "else" are placed last
  function "<"(Left, Right: Transitions) return Boolean is
    use type Compiler_Declarations.Opcode;
    Right_Is_Else: Boolean :=
     Right.Byte_Code(0).Operator  = Compiler_Declarations.logic_else;
    Left_Is_Else: Boolean :=
     Left.Byte_Code(0).Operator  = Compiler_Declarations.logic_else;
  begin
    return
      (Left.Source < Right.Source) or
      (Left.Source = Right.Source  and
       not Left_Is_Else and Right_Is_Else) or
      (Left.Source = Right.Source  and
       not Left_Is_Else and not Right_Is_Else and
         Left.Target < Right.Target);
  end "<";

  -- Sort transitions
  procedure Sort_Transitions is new
    Ada.Containers.Generic_Array_Sort(
      Byte, Transitions, Transition_Array);

  procedure Sort(T: in out Transition_Array) renames Sort_Transitions;

  -- Return an array of the initial states of each process
  function Get_Process_Initials return Byte_Array_Base is
    P: Byte_Array := Zero_Bytes;
  begin
    for I in Byte range 0..Processes-1 loop
      P(I) := Program(I).Initial_State;
    end loop;
    return P;
  end Get_Process_Initials;

  -- Return all transitions whose source state
  --   is a current state of a process in the state vector S
  function Get_All_Locations(S: State_Vectors.State_Vector)
      return Location_Record is
    N: Byte := 0;      -- Number of transitions satisfying the property
    C: Byte;           -- Count of transitions in the process
    L: Location_Record := ((others => <>), 0, 0);
    use type Options.Execution_Type;
  begin
    for P in 0..Processes-1 loop
      C := Program(P).Count-1;

      -- For fairness, remove the null transition from consideration
      if Options.Execution_Mode = Options.Fairness and then
         P /= Never then
        C := C-1;
      end if;

      -- Copy all transitions with Source equal to the current
      --   state for this process in the state vector
      for T in 0 .. C loop
        if Program(P).Transition_List(T).Source = S.Process(P) and
           Program(P).Is_Active then
          if N > Config.Location_Index'Last then
            raise Internal_Error
              with "too many transitions from state";
          end if;
          L.Location_Array(N) := (P, T);
          N := N + 1;
        end if;
      end loop;
    end loop;
    L.Count := N;
    return L;
  end Get_All_Locations;

  -- Remove transition I from location record L
  procedure Remove_Transition(L: in out Location_Record; I: Byte) is
  begin
    if L.Count <= 1 then
      L.Count := 0;
    else
      -- Decrement Never_Index if removing non-never transition
      if  Automata.Never /= None and then
          L.Never_Index /= None and then
          L.Location_Array(I).Process /= Automata.Never then
        L.Never_Index := L.Never_Index - 1;
      end if;

      -- Move all the subsequent transitions
      L.Location_Array(I..L.Count-2) := L.Location_Array(I+1..L.Count-1);
      L.Count := L.Count - 1;

      -- Check if no more never transitions
      if L.Never_Index /= None and then L.Never_Index = L.Count then
        L.Never_Index := None;
      end if;
    end if;
  end Remove_Transition;

  -- Extract a Byte_Code array of Size from a string S,
  --   which is the sequence of byte codes without the braces
  procedure Extract_Byte_Code(
      S: in String; Size: out Byte; Byte_Code: out Byte_Code_Array) is
    Start: Positive := S'First;  -- Start index of current search
    Stop:  Positive;             -- Stop index in the current search             
    use Ada.Strings.Fixed;
  begin
    Size := 0;
    while Start < S'Last loop
      if Size > Config.Byte_Code_Index'Last then
        raise Unexpected_Input with "too many byte codes";
      end if;

      -- The opcode ends with a blank
      Stop := Index(S, " ", Start);
      Byte_Code(Size).Operator  := 
        Compiler_Declarations.Opcode'Value(S(Start .. Stop-1));

      -- The first operand ends with a blank
      Start := Stop + 1;
      Stop := Index(S, " ", Start);
      Byte_Code(Size).Operand1 := Byte'Value(S(Start .. Stop-1));

      -- The second operand ends with a comma
      Start := Stop + 1;
      Stop := Index(S, ",", Start);
      Byte_Code(Size).Operand2 := Byte'Value(S(Start .. Stop-1));
      Start := Stop + 1;
      Size := Size + 1;
    end loop;
  end Extract_Byte_Code;

  -- Create a transition by extracting data from string S
  function Set_Transition(S: in String) return Transitions is
    T: Transitions;
    B: Byte_Code_Array;
    use Utilities;
  begin
    T.Source       := Extract(S, "source");
    T.Target       := Extract(S, "target");
    T.Atomic       := Extract(S, "atomic");
    T.End_Label    := Extract(S, "end");
    T.Accept_Label := Extract(S, "accept");
    T.Line_Number  := Extract(S, "line");
    T.Statement    := new String'(
      Pad(Extract_Paren(S, "statement"), Count=>Line'Length));
    Extract_Byte_Code(
      Extract_Paren(S, "byte code"), T.Code_Size, B);
    T.Byte_Code    := new Byte_Code_Array'(B);
    return T;
  end Set_Transition;

  -- Replicate proctype
  procedure Replicate_Proctype(
      Proc: in Byte; Copy: in Byte) is
    use Utilities;
    Save_Never: Process_Type;
  begin -- Replicate_Proctype
    if Processes > Config.Process_Index'Last then
      raise Internal_Error with "too many processes";
    end if;

    if Never /= None then
      Save_Never := Program(Never);
      Processes  := Processes - 1;
    end if;

    Program(Processes) := Program(Proc);
    Program(Processes).Identifier :=
      Pad(Trim(Program(Proc).Identifier) & "_" & Trim(Byte'Image(Copy)));
    Program(Processes).Is_Active  := True;
    Program(Proc).Copies          := Program(Proc).Copies + 1;
    Program(Processes).PID        := PID_Counter;
    PID_Counter                   := PID_Counter + 1;
    Symbol_Tables.Set_Local(Program(Processes).Variables);
    Processes                     := Processes + 1;

    -- Check if there is enough room in the state vector
    State_Stack.Check_Sizes(Processes, Symbol_Tables.Get_Data_Size);

    if Never /= None then
      Program(Processes) := Save_Never;
      Never := Processes;
      Processes  := Processes + 1;
    end if;
  end Replicate_Proctype;

  -- Read the automata from the automata file
  procedure Read(Automata_File: in Ada.Text_IO.File_Type) is
    S:           String(Config.Line_Index); -- String for Get_Line
    Length:      Natural;                   -- Length for Get_Line
    Active_Flag: Byte;
    use Ada.Text_IO, Options, Utilities;
  begin
    while not End_Of_File(Automata_File) loop
      Get_Line(Automata_File, S, Length);

      -- List of transitions for a process
      if Ada.Strings.Fixed.Index(S, "process=") = 1 then
        declare
          P: Process_Type renames Program(Processes);
        begin
          P.Identifier    := Pad(Extract(S, "process"));
          P.Initial_State := Extract(S,     "initial");
          P.Count         := Extract(S,     "transitions");
          P.Variables     := Extract(S,     "local_variables");
          Active_Flag     := Extract(S,     "active");
          if Active_Flag > 0 then
            P.Copies    := Active_Flag;
            P.Is_Active := True;
          end if;

          if P.Count > Config.Transition_Index'Last+1 then
            raise Unexpected_Input with "too many transitions in a process";
          end if;

          -- Read all the transitions
          for I in 0 .. P.Count-1 loop
            Get_Line(Automata_File, S, Length);
            P.Transition_List(I) := Set_Transition(S);
          end loop;

          Sort(P.Transition_List(0..P.Count-1));

          -- Create a dummy transition transition where a null
          --  transition will be built for blocked processes
          --  when verifiying with fairness; see SMC, p. 183
          if Options.Execution_Mode = Options.Fairness then
            P.Transition_List(Byte(P.Count)) :=
              (Statement => new String'(
                              Utilities.Pad("null",
                              Count=>Global.Line'Length)),
               Code_Size => 1,
               Byte_Code => new Byte_Code_Array'(
                              (Compiler_Declarations.noop, 0, 0),
                              others => <>),
               others => 0);
             P.Count := P.Count + 1;
          end if;
        end;

        Processes := Processes + 1;

      -- Read symbol table data
      elsif Ada.Strings.Fixed.Index(S, "symbol=") = 1 then
        Symbol_Tables.Set_Symbol(S);
      elsif Ada.Strings.Fixed.Index(S, "global_variables=") = 1 then
        Symbol_Tables.Set_Global(S);
      elsif Ada.Strings.Fixed.Index(S, "number=") = 1 then
        Symbol_Tables.Set_Number(S);
      elsif Ada.Strings.Fixed.Index(S, "string=") = 1 then
        Symbol_Tables.Set_String(S);
      elsif Ada.Strings.Fixed.Index(S, "channel=") = 1 then
        Symbol_Tables.Set_Channel(S);
      elsif Ada.Strings.Fixed.Index(S, "mtype=")  = 1 then
        Symbol_Tables.Set_MType(S);
      end if;
    end loop;

    -- Ensure that "init" is assigned pid=0
    --   Then assign other pid's
    -- When a pid is assigned, set the "frame" table with
    --   an entry for the size of the local variables
    for I in 0..Processes-1 loop
      if Program(I).Identifier(1..4) = "init" then
        Program(I).PID := 0;
        PID_Counter := 1;
        Symbol_Tables.Set_Local(Program(I).Variables);
      end if;
    end loop;

    for I in 0..Processes-1 loop
      if Program(I).Identifier(1..4) /= "init" and then 
         Program(I).Is_Active then
        Program(I).PID := PID_Counter;
        PID_Counter := PID_Counter + 1;
        Symbol_Tables.Set_Local(Program(I).Variables);
      end if;
    end loop;

    -- For active[N] proctype, replicate the additional processes
    for P in 0..Processes-1 loop
      if Program(P).Copies > 1 then
        for C in 1..Program(P).Copies-1 loop
          Replicate_Proctype(P, C);
        end loop;
      end if;
    end loop;

    -- Check if there is enough room in the state vector
    State_Stack.Check_Sizes(Processes, Symbol_Tables.Get_Data_Size);
  exception
    when E:others =>
      raise Unexpected_Input with "automata file error: " &
            Ada.Exceptions.Exception_Name(E) & ":" &
            Ada.Exceptions.Exception_Message(E);
  end Read;

  -- Cache process/state pairs that are accepting for efficiency
  procedure Set_Accept_Transitions is
    P: Byte := Processes - 1;   -- Index of current process
    Exists: Boolean;            -- Flag if state already exists
  begin
    for T in 0..Program(P).Count-1 loop
       if Program(P).Transition_List(T).Accept_Label = 1 then
         Exists := False;
         for A in 0 .. Accept_Count-1 loop
           if Accept_Table(A) =
             (P, Program(P).Transition_List(T).Source) then
             Exists := True;
             exit;
           end if;
         end loop;
         if not Exists then
           Accept_Table(Accept_Count) :=
             (P, Program(P).Transition_List(T).Source);
           Accept_Count := Accept_Count + 1;
         end if;
       end if;
    end loop;
  end Set_Accept_Transitions;

  -- Translate LTL formula into transitions
  --   Read the LTL formula from a file
  procedure Translate_LTL is
    LTL_Transitions: Transition_Array := LTL.LTL_To_Automaton;
    Count: Byte := LTL_Transitions'Length;
  begin
    if Count > Config.Transition_Index'Last then
      raise Internal_Error with "too many transitions for LTL formula";
    -- The LTL formula will add a process; check if there is room
    elsif Processes > Config.Process_Index'Last then
      raise Internal_Error with "too many processes";
    end if;

    -- Store the transitions in the Program table as an addition process
    Program(Processes) := (
      Identifier        => Utilities.Pad(":never:"),
      Transition_List   =>
        LTL_Transitions &
        Transition_Array'(Count..Config.Transition_Index'Last => <>),
        Initial_State   => 0,
        Is_Active       => True,
        Count           => Count,
        others          => <>);

    -- This process is the never process
    Never := Processes;
    Processes := Processes + 1;
    Set_Accept_Transitions;
  end Translate_LTL;
end Automata;
