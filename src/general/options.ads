-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
-- Run-time options
--
package Options is
  Error_Number:       Natural;   -- Stop after this error number
  Location_Stack_Max: Positive;  -- Size of location stack
  Progress_Steps:     Positive;  -- Steps per progress notification
  Seed:               Integer;   -- Random simulation seed
  State_Stack_Max:    Positive;  -- Size of state stack
  Total_Steps:        Positive;  -- Maximum steps
  Trail_Number:       Natural;   -- Number of trail file for guided sim

  -- 2**Hash_Slots is the number of slots in the hash table
  Hash_Slots:         Positive range 16..32;

  -- Execution mode
  type Execution_Type is
    (Simulation, Safety, Acceptance, Fairness, Compile_Only);
  Execution_Mode: Execution_Type;

  -- LTL mode: internal or from a file or default rule
  type LTL_Type is (None, Internal, File, Default_LTL);
  LTL_Mode: LTL_Type;

  -- Do not stop on end state
  No_Stop_On_End_State: Boolean;

  -- Simulation mode
  type Simulation_Type is (Random, Interactive, Guided);
  Simulation_Mode: Simulation_Type;

  -- Display option flags
  type Display_Type is
    (All_T, Byte_Codes, Channels, Chosen, Executable, Hash, LTL,
     Location_Stack, Nodes, Program, Run,
     Progress, Simulation_States, State_Stack, Trail, Version);
  Display: array(Display_Type) of Boolean;

  -- Display option flags
  type Debug_Type is
    (Debug_Parser, Debug_Interpreter, Debug_Preprocessor);
  Debug: array(Debug_Type) of Boolean;

  -- Put the options
  procedure Put_Options;

  -- Set default options before reading arguments
  procedure Set_Defaults;
end Options;
