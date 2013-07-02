-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Execute the model checker
--  This package is the parent of the child packages for
--    simulation, verification and byte-code interpretation.
--
with Ada.Text_IO;
with Automata, Global, State_Vectors;
package Execute is
  -- Execute a simulation or verification
  procedure Run;
private
  -- End state: valid, invalid or the completion of a never claim
  type End_Type is (Valid, Invalid, Never);

  Atomic:    Global.Byte;                -- Process executing atomic
  Current:   State_Vectors.State_Vector; -- Current state
  End_State: End_Type;                   -- End state status
  Handshake: Global.Byte;                -- For rendezvous channels
  L_Rec:     Automata.Location_Record;   -- Locations from Current
  Unfolded:  Global.Byte;                -- Copies for checking fairness

  -- Increment the step counter
  procedure Increment_Steps;

  -- Execute the transition at location L
  procedure Execute_At(L: in Automata.Location_Type);

  -- Execute the transition T of the never claim
  procedure Execute_Never(T: in Global.Byte);

  -- Compute read-only variable _nr_pr
  function Compute_NRPR return Global.Byte;

  -- Return in location record L_Rec the transitions
  --   that are executable in the Current state
  --   and an indication of the End_State status
  procedure Get_Executable_Transitions;
end Execute;
