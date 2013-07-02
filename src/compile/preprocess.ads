-- Copyright 2011 by  Mordechai (Moti) Ben-Ari. See version.ads
package Preprocess is
  -- Preprocess a Promela program
  procedure Preprocess_File;

  -- Replace defined symbols in LTL formula
  procedure Use_Inline(Is_Define: Boolean; Start_From: Natural := 0);
end Preprocess;
