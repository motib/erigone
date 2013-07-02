-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Evaluate an expression
--
with Automata, Global, State_Vectors;
package Execute.Statement is
  -- Evaulate the byte Code (of length Size) in the Current state
  -- For a statement, it also updates the state vector
  --   so the parameter Current is of mode in-out
  -- The Result of an expression is returned to the caller
  --   (1 for a statement that does not evaluate an expression)
  -- Process_ID is used for computing "_pid" and
  --   as the index for the frame of local variables
  -- Extra is the channel index for and array of channels
  procedure Evaluate(
    Current:    in out State_Vectors.State_Vector; 
    Size:       Global.Byte;
    Code:       access Automata.Byte_Code_Array;
    Process_ID: Global.Byte;
    Extra:      Global.Byte;
    Result:     out Integer);
end Execute.Statement;
