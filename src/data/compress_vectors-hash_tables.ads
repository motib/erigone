-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Hash table of state vectors
--
with State_Vectors;
package Compress_Vectors.Hash_Tables is
  procedure Initialize;

  -- Put the state vector S in the hash table,
  --   return if it was Inserted or not (because it was already there)
  procedure Put_State(
    S:        in State_Vectors.State_Vector;
    Inserted: out Boolean);

  -- Put hash table statistics at end of execution
  procedure Put_Hash;
end Compress_Vectors.Hash_Tables;
