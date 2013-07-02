-- Copyright 2011-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Ada.Text_IO;       use Ada.Text_IO;
with Utilities; use Utilities;
package body Model_Data is
  procedure Debug is
    T: Natural;
  begin
    -- Put flags
    Put_Line("Fairness  : " & Boolean'Image(Fairness));
    Put_Line("Simulation: " & Boolean'Image(Simulation));

    -- Put variable names
    Put("Variables: ");
    for V in 0..Variables-1 loop
      Put(Trim(Variable_Table(V)) & ", ");
    end loop;
    New_Line;

    -- Put process names and transition data
    for P in 0..Processes-1 loop
      Put_Line("Process: " & Trim(Process_Table(P)));
      T := 0;
      loop
        declare
          TT: Transition_Type renames Transition_Table(P, T);
        begin
          exit when TT.Statement = Blanks;  -- Unused elements are blank
          Put_Line(
            Trim_Int(TT.Source) & "->" & Trim_Int(TT.Target) &
            ", accept=" & Trim_INt(TT.Accept_Label) &
            ", end=" & Trim_Int(TT.End_Label) & ": " &
            Trim_Int(TT.Line_Number) & ". " & Trim(TT.Statement) );
          T := T + 1;
        end;
      end loop;
    end loop;
  end Debug;

  -- Get the data from the trc file
  procedure Read_Model is
    S:           Global.Line; -- Buffer for input of line
    Length:      Natural;     -- Length of input from Get_Line
    T_Count:     Natural;     -- Number of transitions in a process
    Never_Count: Natural;     -- Number of never transitions
  begin
    Get_Line(Trace_File, S, Length);
    -- Set fairness and simulation flags from the first line of the file
    Fairness   := Trim(Extract(S, "execution mode")) = "fairness";
    Simulation := Trim(Extract(S, "execution mode")) = "simulation";

    -- Skip until start of symbol table
    loop
      Get_Line(Trace_File, S, Length);
      exit when S(1..19) = "symbol table start=";
    end loop;

    -- Get number of variables and their names
    Get_Line(Trace_File, S, Length);
    Variables := Extract(S, "variables");
    for I in 0..Variables-1 loop
      Get_Line(Trace_File, S, Length);
      Variable_Table(I) := Extract(S, "name");
    end loop;

    -- If fairness, add dummy variable "fair" to the table
    if Fairness then
      Variable_Table(Variables) := Pad("fair");
      Variables := Variables + 1;
    end if;

    -- Skip to transitions
    loop
      Get_Line(Trace_File, S, Length);
      exit when S(1..18) = "transitions start=";
    end loop;

    -- Get number of processes
    Get_Line(Trace_File, S, Length);
    Processes := Extract(S, "processes");
    Never_Count := 0;   -- No never transitions for now

    -- For each process get its transitions
    for I in 0..Processes-1 loop
      Get_Line(Trace_File, S, Length);
      Process_Table(I) := Extract(S, "process");

      -- If this is the never process, set Never_Count to 1
      if Trim(Process_Table(I)) = ":never:" then
        Never_Count := 1;
      end if;

      -- Get the number of transitions in the process and their data
      T_Count := Extract(S, "transitions");
      for J in 0..T_Count-1 loop
        Get_Line(Trace_File, S, Length);
        Transition_Table(I, J) :=
          Transition_Type'(
            Pad(Extract_Paren(S, "statement")),
            Extract(S, "line"),
            Extract(S, "source"),
            Extract(S, "target"),
            Extract(S, "end"),
            Extract(S, "accept")
          );

        -- Replace blank statement by "(end)"
        if Transition_Table(I, J).Statement = Blanks then
          Transition_Table(I, J).Statement := Pad("(end)");
        end if;

        -- Arbitrary line numbers to transitions of the never process
        if Never_Count > 0 then
          Transition_Table(I, J).Line_Number := Never_Count;
          Never_Count := Never_Count + 1;
        end if;
      end loop;
    end loop;

    -- Print debug information if requested
    if Global.DEBUG then Debug; end if;
  end Read_Model;
end Model_Data;
