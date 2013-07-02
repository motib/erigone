-- Copyright 2008-11 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Automata resulting from the compilation of the Promela source
--    To keep the package body of reasonable size,
--    display subprograms are placed in the child package Display
--
with Ada.Text_IO;
with Compiler_Declarations, Config, State_Vectors;
with Global; use Global;
package Automata is
  -- Byte code type and byte code array type
  type Byte_Code is
    record
      Operator: Compiler_Declarations.Opcode := Compiler_Declarations.noop;
      Operand1: Byte := 0;
      Operand2: Byte := 0;
    end record;
  type Byte_Code_Array is array(Config.Byte_Code_Index) of Byte_Code;

  -- Transitions
  --   When going from Source to Target, Statement at Line_Number
  --     is evaluated (if an expression) or executed,
  --     using the Byte_Code that it was compiled to
  --   Atomic, End_Label, Accept_Label are Promela flags
  --   Access types used for Statement and Byte Code
  --     to save allocating more memory than is needed
  type Transitions is
    record
      Statement:    access Line;
      Source:       Byte;
      Target:       Byte;
      Atomic:       Byte;
      End_Label:    Byte;
      Accept_Label: Byte;
      Line_Number:  Byte;
      Code_Size:    Byte;
      Byte_Code:    access Byte_Code_Array;
    end record;

  -- Redefine "=" because of access types and code size
  function "="(Left, Right: Transitions) return Boolean;

  -- Unconstrained array of transitions
  type Transition_Array is array(Byte range <>) of Transitions;

  -- A location is a transition out of a state for a process
  --   It consists of a process index and
  --     an index for a transition of that process
  type Location_Type is
    record
      Process:    Byte := 0;
      Transition: Byte := 0;
    end record;

  -- Array of locations
  type Location_Array_Type is array(Config.Location_Index) of Location_Type;

  -- Record of locations:
  --   An array of locations, a Count of the locations in the array and
  --   the index of first location from a never claim (which are
  --   always last in the record)
  -- Location_Record is used for "all transitions" and
  --   "executable transitions" from a state
  type Location_Record is
    record
      Location_Array: Location_Array_Type;
      Count:          Byte;
      Never_Index:    Byte := None;
    end record;

  -- A process consists of an Identifier, an Initial_State and the PID
  --   Is_Active is used to ignore non-activated processes
  --   Copies keeps track of copies for "run"
  --   Variables is the size of the local variables
  --   Transition_List is the set of transitions
  --     and Count is the number of transitions
  type Process_Type is
    record
      Identifier:      Name    := Blanks;
      Initial_State:   Byte    := 1;
      PID:             Byte    := None;
      Is_Active:       Boolean := False;
      Copies:          Byte    := 0;
      Variables:       Byte    := 0;
      Count:           Byte    := 0;
      Transition_List: Transition_Array(Config.Transition_Index);
    end record;

  -- A program is an array of processes
  Program: array(Config.Process_Index) of Process_Type;

  -- Cache process/state pairs that are accepting for efficiency
  type Accept_State is
    record
      Process: Byte;
      State:   Byte;
    end record;
  Accept_Table: array(Byte) of Accept_State;

  -- Global counters and indices

  -- Number of processes
  Processes: Byte;

  -- Index of never claim process (it is always the last one)
  Never:     Byte;

  -- The number of accept transitions
  Accept_Count: Byte;

  procedure Initialize;

  -- Sort the transitions
  --   See the pacakge body for the comparison function
  procedure Sort(T: in out Transition_Array);

  -- Replicate process
  procedure Replicate_Proctype(Proc: in Byte; Copy: in Byte);

  -- Return an array of the initial states of each process
  function Get_Process_Initials return Byte_Array_Base;

  -- Return all transitions whose source state
  --   is a current state of a process in the state vector S
  function Get_All_Locations(S: State_Vectors.State_Vector)
    return Location_Record;

  -- Remove location I from Location_Record L
  procedure Remove_Transition(L: in out Location_Record; I: Byte);

  -- Extract the byte code array from a string
  procedure Extract_Byte_Code(
      S: in String; Size: out Byte; Byte_Code: out Byte_Code_Array);

  -- Read the automata from the automata file
  procedure Read(Automata_File: in Ada.Text_IO.File_Type);

  -- Translate the LTL into a BA and store as never claim transitions
  procedure Translate_LTL;
end Automata;
