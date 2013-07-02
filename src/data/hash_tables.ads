-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Hash table of state vectors
--  This package renames the subprograms of Compress_Vectors.Hash_Tables
--    _in the package body_ so that Execute.Verify is not
--    semantically dependent on Compress_Vectors
--
with State_Vectors;
package Hash_Tables is
  procedure Initialize;

  -- Put the state vector S in the hash table,
  --   return if it was Inserted or not (because it was already there)
  procedure Put_State(
    S:        in State_Vectors.State_Vector;
    Inserted: out Boolean);

  -- Put the hash table statistics at the end of the execution
  procedure Put_Hash;
end Hash_Tables;
