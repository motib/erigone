-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Stack for locations (transitions)
--
with Automata, Global;
package Location_Stack is
  -- Stack elements are of type Location_Item
  --   L is the location counter for the process
  --   Never is the never-claim transition in the synchronous automaton
  --   Visited is true if the location was used to create new states
  --   Last is true if this is the last location for this state
  type Location_Item is
    record
      L:       Automata.Location_Type;
      Never:   Global.Byte := 0;
      Visited: Boolean     := False;
      Last:    Boolean     := False;
    end record;

  procedure Initialize;
  procedure Push(S: in Location_Item);
  procedure Pop;
  function  Top return Location_Item;
  function  Empty return Boolean;

  -- Set the Visited flag on the top element of the stack
  procedure Set_Visited;

  -- Put statistics on the use of the stack
  procedure Put_Stack;

  -- Write the trail from the location stack
  --   Error_Count is used for file name if writing all trails
  --   Start_Of_Accept_Cycle is the index of the stack element that
  --     starts the accept cycle (or -1)
  procedure Put_Trail(
    Error_Count:               in Positive;
    Start_Of_Acceptance_Cycle: in Integer;
    Never_Claim_Terminated:    in Boolean);
end Location_Stack;
