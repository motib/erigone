-- Copyright 2011-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
--
-- Read the model data from the trace file:
--   the names of the variables
--   the names of the processes
--   the transitions:
--     line number, statement, source, target, accept and end flags
--
--   from the execution mode in the first line, set the fairness flag
--
with Global; use Global;
package Model_Data is
  -- Names of variables
  Variable_Table: array(Variable_Index) of Name;
  Variables:      Variable_Index;

  -- Names of processes
  Process_Table:  array(Process_Index) of Name;
  Processes:      Process_Index;

  -- Mode flags
  Fairness:       Boolean;
  Simulation:     Boolean;

  -- Transition record
  type Transition_Type is
    record
      Statement:    Name := Blanks;
      Line_Number:  Natural;
      Source:       Natural;
      Target:       Natural;
      End_Label:    Natural range 0..1;
      Accept_Label: Natural range 0..1;
    end record;

  -- Data on transitions
  Transition_Table:
    array(Process_Index, Transition_Index) of Transition_Type;

  -- Get model data from the trc file
  procedure Read_Model;
end Model_Data;
