-- Copyright 2009 by  Mordechai (Moti) Ben-Ari. See version.ads
package State is
  -- Compile a statement
  procedure Statement;

  -- Fix forward goto's
  procedure Fix_Gotos;

  -- Initialize a new transition with source state S and target state T
  procedure Init_Transition (S, T : in Integer);

  procedure Initialize;
end State;
