-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Convert the tableau nodes to a Buchi automaton.
--
with Automata, Global;
private package LTL.Automaton is
  -- N_Set is the set of nodes of the tableau
  -- LTL_Transitions is the array of transitions that is returned
  -- Count is the number of transitions in LTL_Transitions
  procedure Convert(
      N_Set:           in  Node_Sets.Set;
      LTL_Transitions: out Automata.Transition_Array;
      Count:           out Global.Byte);
end LTL.Automaton;
