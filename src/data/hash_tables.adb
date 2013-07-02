-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Compress_Vectors.Hash_Tables;
package body Hash_Tables is
  procedure Initialize renames Compress_Vectors.Hash_Tables.Initialize;

  -- Put the state vector S in the hash table,
  --   return if it was Inserted or not (because it was already there)
  procedure Put_State(
    S:        in State_Vectors.State_Vector;
    Inserted: out Boolean)
      renames Compress_Vectors.Hash_Tables.Put_State;

  -- Put the hash table statistics at the end of the execution
  procedure Put_Hash renames Compress_Vectors.Hash_Tables.Put_Hash;
end Hash_Tables;
