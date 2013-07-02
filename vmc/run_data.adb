-- Copyright 2011-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Utilities;  use Utilities;
with Model_Data, Generate_Space;

package body Run_Data is
  -- Count of graphs
  Count:     Natural;

  -- Current state and edge being processed
  Current_State: Integer;
  Current_Edge:  Integer;

  -- S is the trace line being processed
  procedure Debug(S: in String; L: in Natural) is
    use Ada.Text_IO;
  begin
    -- Separator between data from different files
    Put_Line("************");

    -- Graph counter
    Put_Line("Count =" & Natural'Image(Count));

    -- Print the line that gives rise to the graph
    Put_Line(S(S'First..L));

    -- Print each state 
    Put_Line("States");
    for I in 0..States-1 loop
      declare
        S: State_Record renames State_Table(I);
      begin
        Put_Line(Trim(S.N)   &
                 " Stack="   & Boolean'Image(S.Stack)   & 
                 " Matched=" & Boolean'Image(S.Matched) & 
                 " Current=" & Boolean'Image(S.Current) &
                 " Error="   & Boolean'Image(S.Error)   &
                 " Inner="   & Boolean'Image(S.Inner)   &
                 " Visits="  & Integer'Image(S.Visits));
        -- For the current state, display the executable transitions
        if Model_Data.Simulation and then S.Current then
          Put_Line("Executable transitions =" & Natural'Image(S.Exec));
          for J in reverse 0..S.Exec-1 loop
            Put_Line("process=" & Trim(S.Ex_Array(J).Process) &
                     ",source=" & Natural'Image(S.Ex_Array(J).Source) &
                     ",target=" & Natural'Image(S.Ex_Array(J).Target));
          end loop;
        end if;
      end;
    end loop;

    -- Print each edge
    Put_Line("Edges");
    for I in 0..Edges-1 loop
      Put_Line(Trim(
        Natural'Image(Edge_Table(I).Source) & "->" &
        Natural'Image(Edge_Table(I).Target) 
      ));
    end loop;
  end Debug;

  -- Return the index of the existing state whose name is S
  function Search_State(S: String) return Integer is
  begin
    for I in 0..States-1 loop
      if State_Table(I).N = Pad(S) then return I; end if;
    end loop;
    return -1; 
  end Search_State;

  -- Return the index of the existing edge
  function Search_Edge(S, T: Natural) return Integer is
  begin
    for I in 0..Edges-1 loop
      if Edge_Table(I) = (S, T) then return I; end if;
    end loop;
    return -1;
  end Search_Edge;

  -- Read the trace of the search for a verification and store 
  procedure Read_Verification_Data is
    S:         Line;            -- Input line buffer
    Length:    Natural;         -- Length of input line
    Comma:     Natural;         -- Location of char after first comma
    Write_Dot: Boolean;         -- Should this be written to dot file?
    Last_Top:  Boolean;         -- Don't process multiple "top state"
  begin
    -- Initialize: no current state and edge, zero other variables
    Current_State := -1;
    Current_Edge  := -1;
    Count    := 0;
    States   := 0;
    Edges    := 0;
    Last_Top := False;

    loop
      -- Read line, exit when verification terminated
      Ada.Text_IO.Get_Line(Trace_File, S, Length);
      exit when Index(S, "verification terminated=") /= 0;

      -- Find location of character after first comma
      Comma := Index(S, ",") + 1;

      -- "inserted" and "seed" (acceptance) are new or matched states
      if Index(S, "inserted=") /= 0 or else Index(S, "seed=") /= 0 then

        -- New state, enter its name in the state table
        --   Turn on Inner flag for "seed"
        if Index(S, "inserted=true") /= 0 or else
            Index(S, "seed=") /= 0 then
          State_Table(States) := (Pad(S(Comma..Length)), others => <>);
          if Index(S, "seed=") /= 0 then
            State_Table(States).Inner := True;
          end if;
          States := States + 1;
          Last_Top := False;
          Write_Dot := False;

        -- Existing state, turn on Matched flag for this state
        else     -- "inserted=false"
          State_Table(Search_State(S(Comma..Length))).Matched := True;
          Write_Dot := True;
        end if;

        -- If not initial state, create edge from current state to here
        if Current_State /= -1 then
          Edge_Table(Edges) :=
            (Current_State, Search_State(S(Comma..Length)));
          Edges := Edges + 1;
        end if;

      -- "top state" (but previous graph was not for a "top state"),
      --    Search for this state and set current state to it
      --    Turn Current flag on for this state and off for previous one 
      elsif Index(S, "top state=") /= 0 and not Last_Top then
        if Current_State /= -1 then
          State_Table(Current_State).Current := False;
        end if;
        Current_State := Search_State(S(Comma..Length));
        State_Table(Current_State).Current := True;
        Last_Top := True;
        Write_Dot := True;

      -- "push state", turn on Stack flag
      elsif Index(S, "push state=") /= 0 then
        State_Table(Search_State(S(Comma..Length))).Stack := True;
        Last_Top := False;
        Write_Dot := False;

      -- "pop state", turn off Stack flag in current state
      elsif Index(S, "pop state=") /= 0 then
        State_Table(Current_State).Stack := False;
        Last_Top := False;
        Write_Dot := False;

      -- "current state matches stack element" is the indication
      --   of an accept cycle
      -- Create back edge and turn Inner flag on for matched state
      elsif Index(S, "current state matches stack element=") /= 0 then
        State_Table(Search_State(S(Comma..Length))).Inner := True;
        Edge_Table(Edges) :=
          (Current_State, Search_State(S(Comma..Length)));
        Edges := Edges + 1;
        Write_Dot := True;

      -- For other lines in the trace, don't write to a dot file
      else
        Write_Dot := False;
      end if;

      if Write_Dot then
        if Global.DEBUG then Debug(S, Length); end if;
        Generate_Space.Put_Dot_File(Count);
        Count := Count + 1;
      end if;
    end loop;

    -- Verification terminated:
    --   Write one more dot file with Error indication on current state
    --     for assert violation and on last state for others
    declare
      S1: String := Trim(Extract(S, "verification terminated"));
    begin
      if S1 = "successful" then
        return;
      elsif S1 = "assert statement is false" then
        State_Table(Current_State).Error := True;
      elsif S1 = "invalid end state" then
        State_Table(States-1).Error := True;
      elsif S1 = "acceptance cycle" then
        State_Table(States-1).Error := True;
      end if;
      if Global.DEBUG then Debug(S, Length); end if;
      Generate_Space.Put_Dot_File(Count);
      Count := Count + 1;
    end;
  end Read_Verification_Data;

  -- Read the trace of a simulation and store 
  procedure Read_Simulation_Data is
    S:         Line;      -- Input line buffer
    Length:    Natural;   -- Length of input line
    Comma:     Natural;   -- Location of char after first comma
    Write_Dot: Boolean;   -- Should this be written to dot file?
    New_State: Integer;   -- The "initial" or new "next" state read
    Ex_Count:  Natural;   -- Count of executable transitions
  begin
    -- Initialize: no current state and edge, zero other variables
    Current_State := -1;
    Current_Edge  := -1;
    Count    := 0;
    States   := 0;
    Edges    := 0;

    loop
      -- Read line, exit when verification terminated
      Ada.Text_IO.Get_Line(Trace_File, S, Length);
      exit when Index(S, "simulation terminated=") /= 0;

      -- Find location of character after first comma
      Comma := Index(S, ",") + 1;

      -- Read an "initial" or "next" state
      if Index(S, "next state=") /= 0 or else
         Index(S, "initial state=") /= 0 then
        New_State := Search_State(S(Comma..Length));

        -- New state, not encountered before, store in state table
        if New_State = -1 then
          State_Table(States) := (Pad(S(Comma..Length)), others => <>);
          New_State := States;
          States := States + 1;
        end if;
        State_Table(New_State).Visits :=
          State_Table(New_State).Visits + 1;
        Write_Dot := False;

        -- If not initial state, create edge from current state to here
        if Current_State /= -1 and then
            Search_Edge(Current_State, New_State) = -1 then
          Edge_Table(Edges) := (Current_State, New_State);
          Edges := Edges + 1;
        end if;

        -- If not initial state, set current state flag to false 
        if Current_State /= -1 then
          State_Table(Current_State).Current := False; 
        end if;
        -- Set the current state to the new state and set flag
        Current_State := New_State;
        State_Table(Current_State).Current := True;

      -- Executable transition: set counter to number of transitions
      elsif Index(S, "executable transitions=") /= 0 then
        Ex_Count := Extract(S, "executable transitions");
        State_Table(Current_State).Exec := Ex_Count;
        Write_Dot := False;

      -- For each executable transition, store in state table
      elsif Ex_Count > 0 and then Index(S, "process=") /= 0 then
        State_Table(Current_State).Ex_Array(Ex_Count-1) :=
          (Pad(Extract(S, "process")),
           Extract(S, "source"),
           Extract(S, "target"));
        Ex_Count := Ex_Count - 1;
        Write_Dot := Ex_Count = 0;
      
      -- For other lines in the trace, don't write to a dot file
      else
        Write_Dot := False;
      end if;

      if Write_Dot then
        if Global.DEBUG then Debug(S, Length); end if;
        Generate_Space.Put_Dot_File(Count);
        Count := Count + 1;
      end if;
    end loop;

    -- Simulation terminated:
    --   Write one more dot file with Error indication on current state
    --     for assert violation and on last state for others
    declare
      S1: String := Trim(Extract(S, "simulation terminated"));
    begin
      if S1 = "successful" then
        return;
      elsif S1 = "assert statement is false" then
        State_Table(Current_State).Error := True;
      elsif S1 = "invalid end state" then
        State_Table(States-1).Error := True;
      end if;
      if Global.DEBUG then Debug(S, Length); end if;
      Generate_Space.Put_Dot_File(Count);
      Count := Count + 1;
    end;
  end Read_Simulation_Data;
end Run_Data;
