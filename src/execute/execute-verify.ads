-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Parent package for verification
--  Its child packages are Verify_Safety and Verify_Acceptance
--
package Execute.Verify is
  procedure Verify;

  -- Put the sizes of the stacks and the hash table
  procedure Put_Sizes;
private
  -- Count of errors encountered for reporting the m'th or all errors
  Error_Count: Natural;

  -- Stack element holding the start of an acceptance cycle (-1 if none)
  Start_Of_Acceptance_Cycle: Integer;

  -- Never claim is terminated (to stop reading trail file)
  Never_Claim_Terminated: Boolean;

  -- The transition where an exception occurred
  Exception_Transition: Automata.Transitions;

  -- When checking copies for fairness, skip over non-active proctypes
  Unfolded_Bias: Global.Byte;

  -- A state is accepting if any the transitions from state S
  --   has an accept label
  function Is_Accept_State(S: State_Vectors.State_Vector)
    return Boolean;

  -- Get the transitions from the current state and push on the stack
  procedure Get_And_Push_Transitions;
end Execute.Verify;
