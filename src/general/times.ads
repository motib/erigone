-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Record and print times of each phase
--
package Times is
  procedure Start;
  procedure End_Compile;
  procedure End_Execute;
  procedure Print_Times;
end Times;
