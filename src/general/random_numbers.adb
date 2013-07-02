-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Calendar, Ada.Numerics.Float_Random;
package body Random_Numbers is
  Gen: Ada.Numerics.Float_Random.Generator;

  -- Get random number between 0 and N-1 using Float_Random
  --   as described in ARM paragraphs A.5.2(50-52)
  function  Get(N: Global.Byte) return Global.Byte is
    use Global;
  begin
    return Byte(Float(N) * Ada.Numerics.Float_Random.Random(Gen)) 
             mod Byte(N);
  end Get;

  -- Reset to Seed; if Seed is -1, reset from Clock
  procedure Reset(Seed: Integer) is
    S: Integer := Seed;
  begin
    if S = -1 then
      S := Natural(Ada.Calendar.Seconds(Ada.Calendar.Clock));
    end if;
    Ada.Numerics.Float_Random.Reset(Gen, S);
  end Reset;
end Random_Numbers;
