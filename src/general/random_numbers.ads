-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Random number generator
--
with Global;
package Random_Numbers is
  -- Get random number between 0 and N-1
  function  Get(N: Global.Byte) return Global.Byte;

  -- Reset to Seed; if Seed is -1, reset from Clock
  procedure Reset(Seed: Integer);
end Random_Numbers;
