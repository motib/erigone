-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO, Ada.Exceptions, Ada.Strings.Fixed;
with Automata.Display, Byte_IO, Hash_Tables, Files;
with Options, Random_Numbers, Utilities;
with Global; use Global;
package body Execute.Simulate is
  -- Trail file for guided simulation
  Trail_File:  Ada.Text_IO.File_Type;
  -- Counter of the number of states
  State_Count:               Positive;
  -- State that starts an accept cycle (or -1); for guided simulation
  Start_Of_Acceptance_Cycle: Integer;

  procedure Initialize is
    use Options;
  begin
    -- Initialize Current state vector
    Current := State_Vectors.Get_Initial_State_Vector;
    if Display(Simulation_States) then
      State_Vectors.Put_State_Vector("initial state=0,", Current);
    end if;
    State_Count := 1;

    -- Mode-dependent initialization
    if Simulation_Mode = Random then
      null;
    elsif Simulation_Mode = Guided then
      -- For -gN: open the N'th trail file
      if Options.Trail_Number /= 0 then
        Files.Trail_File_Name :=
          new String'(Files.Root_File_Name.all &
            Utilities.Trim(Integer'Image(Trail_Number)) &
            Files.Trail_Extension);
      end if;
      Ada.Text_IO.Open(
        Trail_File, Ada.Text_IO.In_File, Files.Trail_File_Name.all);

      -- First line indicates if this is a trail for an acceptance cycle
      --   or not (-1)
      Start_Of_Acceptance_Cycle :=
        Integer'Value(Utilities.Extract(
          Ada.Text_IO.Get_Line(Trail_File), "start of acceptance cycle"));
    end if;
  exception
    when Ada.Text_IO.Name_Error =>
      raise File_Error
        with "trail file not found: " &
        Files.Trail_File_Name.all;
  end Initialize;

  -- Choose one location from executable transitions in L
  -- Choice is according to the mode
  function Get_Location(L: Automata.Location_Record) 
      return Automata.Location_Type is
    use Options;
    N: Byte;   -- Choice for interactive mode
  begin
    -- If there is only one location, there is no choice
    if L.Count = 1 and Simulation_Mode /= Guided then
      return L.Location_Array(0);

    -- If random simulation, choose randomly
    elsif Simulation_Mode = Random then
      return L.Location_Array(Random_Numbers.Get(L.Count));

    -- If interactive simulation, ask the user
    elsif Simulation_Mode = Interactive then
      loop
        Utilities.Put("choose from=", Byte'(0));
        Utilities.Put("to=", L.Count-1);
        Ada.Text_IO.Put_Line("quit=q,");
        declare
          S: String := Ada.Text_IO.Get_Line;
        begin
          if S(1) = 'q' then
            raise Termination_Error with "by user request";
          end if;
          N := Byte'Value(S);
          exit when N < L.Count;
        exception
          when Termination_Error => raise;
          when others => null;   -- For incorrect input, repeat request
        end;
      end loop;
      return L.Location_Array(N);

    -- If guided simulation, read from the trail file
    --   Entries are: Process=p,Transition=t
    elsif Simulation_Mode = Guided then
      declare
        -- Get line from trail file into S
        S:    String := Ada.Text_IO.Get_Line(Trail_File);
        P, T: Byte;  -- Process and transition
      begin
        -- Stop on end of acceptance cycle
        if Ada.Strings.Fixed.Index(S, "end of acceptance cycle=,") /= 0 then
          raise Termination_Error with "end of acceptance cycle";
        end if;
        if Ada.Strings.Fixed.Index(S, "never claim terminated=,") /= 0 then
          raise Termination_Error with "never claim terminated";
        end if;

        -- Indicate if this state starts the acceptance cycle
        if Options.Display(Simulation_States) and then
           Start_Of_Acceptance_Cycle = State_Count then
          Ada.Text_IO.Put_Line(
            "start of acceptance cycle=" &
            Utilities.Trim(Integer'Image(Start_Of_Acceptance_Cycle)) & ",");
        end if;

        P  := Utilities.Extract(S, "process");
        T  := Utilities.Extract(S, "transition");
        -- Search for this pair in the executable transitions
        for I in 0..L.Count-1 loop
          if  P = L.Location_Array(I).Process and
              T = L.Location_Array(I).Transition then
            return L.Location_Array(I);
          end if;
        end loop;
        -- Can't find; something is wrong with the trail file
        raise Internal_Error
          with "trail file error,entry=(" & S & ")";
      end;
    else
      raise Internal_Error with "incorrect simulation mode";
    end if;
  exception
      -- The guided simulation should terminate somehow,
      --   so EOF on the file is an error
      when Ada.Text_IO.End_Error =>
        raise Internal_Error with "unexpected end of trail";
  end Get_Location;

  procedure Simulate is
    L:        Automata.Location_Type;
  begin
    Initialize;
    loop
      Increment_Steps;
      Get_Executable_Transitions;

      -- If no executable transitions, announce end state
      if L_Rec.Count = 0 then
        if End_State = Valid then
          raise Termination_Error with "valid end state";
        else
          raise Counterexample_Error with "invalid end state";
        end if;
      end if;

      -- Get one of the executable locations
      L := Get_Location(L_Rec);
      if Options.Display(Options.Chosen) then
        Ada.Text_IO.Put_Line("chosen transition=,");
        Automata.Display.Put_One_Location(L);
      end if;

      -- Execute it to get new Current state
      Execute_At(L);

      if Options.Display(Options.Simulation_States) then
         State_Vectors.Put_State_Vector(
           "next state=" &
           Utilities.Trim(Integer'Image(State_Count)) & ",", Current);
      end if;
      State_Count := State_Count + 1;
    end loop;
  exception
    when E: others =>
      declare
        -- Get the transition where the exception occurred
        --   so that line number and statement can be printed
        T: Automata.Transitions renames 
          Automata.Program(L.Process).Transition_List(L.Transition);
      begin
        Ada.Text_IO.Put_Line(
          "simulation terminated=" &
          Ada.Exceptions.Exception_Message(E) & "," &
          Utilities.Line_Statement(T.Line_Number, T.Statement.all) & ",");
      end;
  end Simulate;
end Execute.Simulate;
