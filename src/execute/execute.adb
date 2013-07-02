-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Automata.Display, Compiler_Declarations, Options;
with Random_Numbers, Symbol_Tables, Times, Utilities;
with Execute.Statement, Execute.Simulate, Execute.Verify;
package body Execute is
  use Global;
  use type Compiler_Declarations.Opcode, Options.Execution_Type;

  -- Total number of steps in a simulation or a verification
  -- Steps for progress reports in a verification
  Total_Counter, Progress_Counter: Natural;

  -- For checking the end state and computing nrpr
  Save_Rec: Automata.Location_Record; 

  -- Execute a simulation or verification
  procedure Run is
    use Options;
  begin
    Atomic           := Global.None;
    Total_Counter    := 0;
    Progress_Counter := 0;
    Handshake        := 0;
    Random_Numbers.Reset(Seed);

    if Execution_Mode = Simulation then
      -- Always display executable transitions in interactive mode
      if Simulation_Mode = Interactive then
        Display(Executable) := True;
      end if;
      Simulate.Simulate;

    else  -- Execution_Mode is Safety or Acceptance
      Verify.Verify;
    end if;

    if Options.Display(Run) then
      Utilities.Put("steps=", Total_Counter, New_Line => True);
      if Execution_Mode /= Simulation then
        Execute.Verify.Put_Sizes;
      end if;
    end if;
  end Run;

  -- Increment the step counter
  procedure Increment_Steps is
  begin
    Total_Counter := Total_Counter + 1;
    if Total_Counter > Options.Total_Steps then
      raise Termination_Error with "too many steps";
    end if;

    -- Increment and display progress counter
    if Options.Display(Options.Progress) then
      Progress_Counter := Progress_Counter + 1;
      if Progress_Counter = Options.Progress_Steps then
        Utilities.Put("steps=", Total_Counter, New_Line => True);
        Progress_Counter := 0;
        Execute.Verify.Put_Sizes;
        Times.End_Execute;
        Times.Print_Times;
      end if;
    end if;
  end Increment_Steps;

  -- Execute the transition at location L
  procedure Execute_At(L: in Automata.Location_Type) is
    use Compiler_Declarations;
    -- The transition at this location
    T: Automata.Transitions renames
         Automata.Program(L.Process).Transition_List(L.Transition);
    Op: Opcode renames T.Byte_Code(T.Code_Size-1).Operator;
    Result: Integer;  -- The result of evaluating an expression
  begin
    -- Evaluate the byte code
    Statement.Evaluate(
      Current, T.Code_Size, T.Byte_Code, L.Process, 0, Result);

    -- Although assert is always executable,
    --   evaluate first and check if false!
    -- Check if expression or channel instruction returned 0
    -- For always executable statements, skip to changing state
    if Result = 0 then
      if Op = assert then
        raise Counterexample_Error with "assert statement is false";
      elsif Executable(Op) = Expression or Executable(Op) = Channel then
        return;
      end if;
    end if;

    -- Set atomic global variable if this is an atomic transition
    --   d_step sets Atomic = 2 and is currently treated as atomic
    if T.Atomic >= 1 then
      Atomic := L.Process;
    else
      Atomic := Global.None;
    end if;
    Current.Atomic := Atomic;

    -- Update Current with new Target state for this process
    State_Vectors.Update_Process_Location(
      Current, L.Process, T.Target);
  end Execute_At;

  -- Execute the transition T of the never claim
  procedure Execute_Never(T: in Byte) is
  begin
    State_Vectors.Update_Process_Location(
      Current, Automata.Never,
      Automata.Program(Automata.Never).Transition_List(T).Target);
  end Execute_Never;

  function Compute_NRPR return Byte is
    Procs: Byte := Automata.Processes;
    NRPR:  Byte := 0;
    T:     Automata.Transitions;
    L:     Automata.Location_Type;
  begin
    if Automata.Never /= None then Procs := Procs - 1; end if;
    for P in 0..Procs-1 loop
      for I in 0..Save_Rec.Count-1 loop
        L := Save_Rec.Location_Array(I);
        T := Automata.Program(L.Process).Transition_List(L.Transition);
        if L.Process = P and then
           T.Code_Size > 0 and then 
           T.Byte_Code(T.Code_Size-1).Operator /= Compiler_Declarations.halt then
          NRPR := NRPR + 1;
          exit;
        end if;
      end loop;
    end loop;
    return NRPR;
  end Compute_NRPR;

  -- Return in location record L_Rec the transitions
  --   that are executable in the Current state
  --   and an indication of the End_State status
  -- Nested structure:
  --   Get_Executable_Transitions
  --     Remove_Not_Executable
  --       Remove_Else
  --       Choose_From_Atomic
  --       Check_Channel_Executable
  --       Get_Executable_Type
  --       Check_End_State
  --       Is_Always_Executable
  --     Set_Never_Index
  --
  procedure Get_Executable_Transitions is

    -- Remove locations from the record L that are not executable
    --   Assignment, assert, else are always executable
    --   Otherwise, evaluate the expression at the Current state
    --   and call Remove_Else
    procedure Remove_Not_Executable is
      T:        Automata.Transitions;   -- Current transition
      L:        Automata.Location_Type; -- Current location
      I:        Byte := 0;              -- Index for locations
      Result:   Integer;                -- Result of evaluation
      use Compiler_Declarations;
      Executable: Executable_Type;

      -- Get the final Operator of the transition for location L
      function Get_Final_Operator(L: Automata.Location_Type)
          return Compiler_Declarations.Opcode is
        T: Automata.Transitions renames
             Automata.Program(L.Process).Transition_List(L.Transition);
      begin
        return T.Byte_Code(T.Code_Size-1).Operator;
      end Get_Final_Operator;

      -- Remove an else unless it is the only executable transition
      --   for its process. Assumes that the else transition is the
      --   last one for its process (true because they are sorted)
      procedure Remove_Else is
        use type Compiler_Declarations.Opcode;
        I: Byte := 0;
      begin
        while I < L_Rec.Count loop
          if Get_Final_Operator(L_Rec.Location_Array(I)) =
               Compiler_Declarations.logic_else then
            -- Remove if the previous (executable) transition is
            --   for the same process
            if I > 0 and then 
                 L_Rec.Location_Array(I).Process = 
                 L_Rec.Location_Array(I-1).Process then
              Automata.Remove_Transition(L_Rec, I);
              I := I - 1;
            end if;
          end if;
          I := I + 1;
        end loop;
      end Remove_Else;

      -- Remove all transitions except those for the atomic process
      --   and the never claim
      -- The atomic process might be blocked so save the original record
      --   in variable L_Save
      procedure Choose_From_Atomic is
        I:      Byte := 0;
        L_Save: Automata.Location_Record := L_Rec;
      begin
        while I < L_Rec.Count loop
          if L_Rec.Location_Array(I).Process /= Atomic and
             L_Rec.Location_Array(I).Process /= Automata.Never then
            Automata.Remove_Transition(L_Rec, I);
            I := I - 1;
          end if;
          I := I + 1;
        end loop;

        -- Restore the original transitions if there are no executable
        --   transitions or if there are only never-claim transitions
        --   (the first transition is for the never claim)
        if L_Rec.Count = 0 or else
             (Automata.Never /= None and L_Rec.Never_Index = 0) then
          L_Rec := L_Save;
        end if;
      end Choose_From_Atomic;

      -- Check if a channel statement is executable
      --   Set Result to 0/1 accordingly
      -- See SMC, p. 555--556 for executability of rendezvous statements
      procedure Check_Channel_Executable is
        use Compiler_Declarations;
        -- Last byte code is channel operation
        B1:      Automata.Byte_Code := T.Byte_Code(T.Code_Size-1);
        -- Next to last is byte_load for channel variable
        B2:      Automata.Byte_Code := T.Byte_Code(T.Code_Size-2);
        -- Channel index
        Index:   Byte;
        -- Channel index for each receive
        IndexR:  Byte;
        -- The channel
        Ch:      Symbol_Tables.Channel;
        -- Number of messages in the channel in the Current state vector
        Num:     Byte;
        -- Temporary state vector for evaluating receive statements
        Scratch: State_Vectors.State_Vector;
        -- Count of load_address instructions
        Count:   Byte := Ch.Elements;
        -- Temporary for result of evaluate

      begin  -- Check_Channel_Executable
        if B2.Operator = byte_aload then
          -- If channel array, simulate up until channel operation
          Scratch := Current;
          Statement.Evaluate(
            Scratch, T.Code_Size, T.Byte_Code,
            L_Rec.Location_Array(I).Process, 1, Result);
          Index := Byte(Result);
        else
          -- Simulate byte_load to get channel index
          Index := State_Vectors.Get_Byte_Variable_Value(Current, B2.Operand1);
        end if;
        Ch     := Symbol_Tables.Get_Channel(Index);
        Result := 0;  -- Assume not executable and check if it is

        -- Rendezvous channel
        if Ch.Buffer_Size = 0 then
          -- Send is executable as long as rendezvous not initiated:
          --   which is true as long as Handshake is 0
          if B1.Operator = fifo_send and then
             Handshake = 0 then
            -- Check for receive statement for the same channel
            -- Use Save_Rec because receive statement might already
            --   have been removed as unexecutable
            for I in 0 .. Save_Rec.Count-1 loop
              declare
                -- Use shorter name
                TT: Automata.Transitions renames
                  Automata.Program(
                    Save_Rec.Location_Array(I).Process).
                    Transition_List(Save_Rec.Location_Array(I).Transition) ;
              begin
                if TT.Byte_Code(TT.Code_Size-1).Operator =
                     move_fifo_receive then
                  B2 := TT.Byte_Code(TT.Code_Size-2);
                  if B2.Operator = byte_aload then
                    -- If channel array, simulate up until channel operation
                    Scratch := Current;
                    Statement.Evaluate(
                      Scratch, TT.Code_Size, TT.Byte_Code,
                      Save_Rec.Location_Array(I).Process, 1, Result);
                    IndexR := Byte(Result);
                  else
                    -- Simulate byte_load to get channel index
                    IndexR := State_Vectors.Get_Byte_Variable_Value(Current, B2.Operand1);
                  end if;
                  if Index = IndexR then
                     Result := 1;
                    return;
                  end if;
                end if;
              end;
            end loop;

          -- Receive is executable only if a send has already initiated
          --   a rendezvous on this channel,
          --   indicated by setting Handshake to the channel index
          elsif B1.Operator = move_fifo_receive and then
                Handshake = Index then
            Result := 1;
          end if;

        else -- Buffered channel
          Num := State_Vectors.Get_Byte_Variable_Value(Current, Ch.Offset);
          if    B1.Operator in fifo_send .. sorted_send then
            -- Executable if channel is not full
            if Num < Ch.Buffer_Size then Result := 1; end if;

          else -- B1.Operator in move_fifo_receive .. random_poll
            -- Not executable if channel is not empty
            if Num = 0 then return; end if;
            -- Evaluate the statement in a copy of the state
            Scratch := Current;
            Statement.Evaluate(
              Scratch, T.Code_Size, T.Byte_Code,
              L_Rec.Location_Array(I).Process, 0, Result);
            end if;
        end if;
      end Check_Channel_Executable;

      -- End state is invalid unless all transitions are labeled "end"
      -- Transitions have been removed, so check original set in Save_Rec
      procedure Check_End_State is
        Count: Byte := Save_Rec.Count;
      begin
        for I in 0..Save_Rec.Count-1 loop
          if Automata.Program(
               Save_Rec.Location_Array(I).Process).
               Transition_List(Save_Rec.Location_Array(I).Transition).
               End_Label = 1 then
            Count := Count - 1;
          end if;
        end loop;
        if Count /= 0 then End_State := Invalid; end if;
      end Check_End_State;
  
    begin -- Remove_Not_Executable
      End_State := Valid;
      while I < L_Rec.Count loop
        L := L_Rec.Location_Array(I);
        T := Automata.Program(L.Process).Transition_List(L.Transition);
        -- Remove end transitions
        -- End state for never claim is a verification error
        if T.End_Label = 1 and then L.Process = Automata.Never then
          End_State := Never;
          Automata.Remove_Transition(L_Rec, I);
          I := I - 1;
        -- Terminate a process at end label with halt
        elsif T.End_Label = 1 and then
              T.Byte_Code(T.Code_Size-1).Operator =
              Compiler_Declarations.halt then
          Automata.Remove_Transition(L_Rec, I);
          I := I - 1;

        -- Remove transitions from non-activated processes
        elsif not Automata.Program(L.Process).Is_Active then
            Automata.Remove_Transition(L_Rec, I);
            I := I - 1;

        -- Evaluate expression unless always executable
        --   Do not allow rendezvous to be interrupted
        else
          Executable :=
            Compiler_Declarations.Executable(
              Get_Final_Operator(L_Rec.Location_Array(I)));
          if Executable = Always then        -- Do not remove
            if Handshake /= 0 then Result := 0; else Result := 1; end if;
          elsif Executable = Expression then -- Evaluate
            if Handshake /= 0 then Result := 0; 
            else
              Statement.Evaluate(
                Current, T.Code_Size, T.Byte_Code, L.Process, 0, Result);
            end if;
          else -- Executable = Channel       -- Check full/empty
            Check_Channel_Executable;
          end if;

          -- Remove transitions that are not executable
          if Result = 0 then
            Automata.Remove_Transition(L_Rec, I);
            I := I - 1;
          end if;
        end if;
        I := I + 1;
      end loop;

      -- Remove else transitions that are not executable
      if L_Rec.Count > 1 then
        Remove_Else;
      end if;

      -- If the Atomic flag is set for a process, choose only from it
      if Atomic /= None and then L_Rec.Count > 1 then
        Choose_From_Atomic;
      end if;

      -- Check for invalid end state:
      --   If there are _no_ executable transitions and 
      --     we have not already found the end of a never claim
      -- When generating the state space, ignore end states
      --   so that the entire space can be searched and generated
      -- When subsequently running the (guided) simulation,
      --   end states must be checked as usual
      if L_Rec.Count = 0 and then End_State /= Never and then 
         (not Options.No_Stop_On_End_State or else 
          Options.Execution_Mode = Options.Simulation) then
        Check_End_State;
      end if;
    end Remove_Not_Executable;

    -- Index of the first executable transition in the never process
    procedure Set_Never_Index is
    begin
      -- No never claim or no executable transitions or
      --   no executable never transitions
      --   (never transitions are always last)
      if  Automata.Never = None or else
          L_Rec.Count = 0       or else
          L_Rec.Location_Array(L_Rec.Count-1).Process /=
          Automata.Never then
        L_Rec.Never_Index := None;

      -- else search from the beginning for first transition of
      --   the never process
      else
        for I in 0..L_Rec.Count-1 loop
          if L_Rec.Location_Array(I).Process = Automata.Never then
            L_Rec.Never_Index := I;
            return;
          end if;
        end loop;
      end if;
    end Set_Never_Index;

    procedure Reset_Atomic is
      T: Automata.Transitions;
      L: Automata.Location_Type;
    begin
      for I in 0..L_Rec.Count-1 loop
        L := L_Rec.Location_Array(I);
        if L.Process = Atomic then
          T := Automata.Program(L.Process).Transition_List(L.Transition);
          if T.Atomic = 0 then Atomic := None; end if;
        end if;
      end loop;
    end Reset_Atomic;
    
  begin -- Get_Executable_Transitions
    -- Get all the transitions from Current state
    --   and set the index of the first never transition
    L_Rec := Automata.Get_All_Locations(Current);
    Set_Never_Index;

    -- Reset atomic
    if Atomic /= None then
      Reset_Atomic;
    end if;

    if Options.Display(Options.All_T) then
      Ada.Text_IO.Put("all transitions=");
      Automata.Display.Put_All_Locations(L_Rec, Atomic, Handshake);
    end if;

    -- Remove non-executable transitions
    Save_Rec := L_Rec; 
    Remove_Not_Executable;

    if Options.Display(Options.Executable) then
      Ada.Text_IO.Put("executable transitions=");
      Automata.Display.Put_All_Locations(L_Rec, Atomic, Handshake);
    end if;
  end Get_Executable_Transitions;
end Execute;
