-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Child package of Automata for display subprograms
--
with Global;
package Automata.Display is
  -- Put a byte code array
  procedure Put_Byte_Code(
    Code_Size: in Global.Byte; Code: access Byte_Code_Array);

  -- Display one transition
  procedure Put_One_Transition(S: in Transitions);

  -- Display one location
  procedure Put_One_Location(L: in Location_Type);

  -- Display all locations in a record L
  -- Also display the process executing with Atomic set, if any,
  --   and the value of Handshake, if not equal to zero
  procedure Put_All_Locations(
    L: in Location_Record;
    Atomic: in Global.Byte;
    Handshake: in Global.Byte);

  -- Display the automata
  procedure Put_Automata;

  -- Display the automata
  procedure Put_One_Process(P: in Byte);
end Automata.Display;
