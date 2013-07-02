-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
-- Configure the size of the states in the state space
--
with Global;
package Config_State is
  -- Size of processes
  subtype Process_Size_Index  is Global.Byte range 0..7;
  -- Size of data size
  subtype Data_Size_Index     is Global.Byte range 0..63;
end Config_State;
