-- Copyright 2011-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
--
-- Read the trace of the simulation or search for a verification and
--   and store the states and transitions (called edges to avoid
--   confusion with the transitions of the model)

with Global; use Global;
package Run_Data is

  -- State record
  --   The state name consists of the variable names and values
  --     and the process names and the values of their location counters
  --   Flags:
  --     On the stack
  --     Matched a state in the hash table
  --     Current state of the search
  --     Error state (assert is false or bad end state)
  --     State generated during an inner search for acceptance
  --   For a simulation, store:
  --     Visits: the number of times the state is visited
  --     The set if executable transitions in each state

  -- An executable transition is stored as the process name and
  --   the source and target states
  type Executable_Record is
    record
      Process:        Name := Blanks;
      Source, Target: Natural := 0;
    end record;
  type Executable_Array is array(Process_Index) of Executable_Record;

  type State_Record is
    record
      N:        Name;
      Stack:    Boolean := False;
      Matched:  Boolean := False;
      Current:  Boolean := False;
      Error:    Boolean := False;
      Inner:    Boolean := False;
      Visits:   Natural := 0;
      Exec:     Natural := 0;
      Ex_Array: Executable_Array := (others => <>);
    end record;

  State_Table: array(State_Index) of State_Record;
  States:      Natural;

  -- Edges: source and target states
  type Edge_Record is
    record
      Source, Target: Natural;
    end record;

  Edge_Table: array(Edge_Index) of Edge_Record;
  Edges:      Natural;

  procedure Read_Verification_Data;
  procedure Read_Simulation_Data;
end Run_Data;
