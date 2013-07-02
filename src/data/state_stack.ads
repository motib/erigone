-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Stack for state vectors
--
with Global, State_Vectors;
package State_Stack is
  -- Check if the size of the compressed vector is sufficient
  procedure Check_Sizes(
    Processes: in Global.Byte; Data_Size: in Global.Byte);

  procedure Initialize;

  -- Put statistics on the use of the stack
  procedure Put_Stack;

  -- Reasons for popping the stack (for display)
  type Reason_Type is
    (No_More_Transitions, No_Transitions_Available, End_Of_Inner_Search);

  -- Stack operations
  procedure Push(S: in State_Vectors.State_Vector);
  procedure Pop(Reason: in Reason_Type);
  function  Top return State_Vectors.State_Vector;
  function  Empty return Boolean;

  -- An acceptance cycle exists if a state is already on the stack
  --   Returns the stack element or -1 if none
  function  On_Stack(S: in State_Vectors.State_Vector) return Integer;

  -- Returns the matched element for printing
  function  Get_Element(I: in Integer) return State_Vectors.State_Vector;
end State_Stack;
