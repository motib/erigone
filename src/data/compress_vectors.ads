-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
-- Compress state vectors for hash table and stack
--
with Config_State, State_Vectors;
with Global; use Global;
package Compress_Vectors is
  type Compressed_Vector is private;

  -- Check that the processes and data can fit
  --   into a compressed vector
  procedure Check_Sizes(Processes: in Byte; Data_Size: in Byte);

  -- Compress/Expand State_Vector <-> Compressed_Vector
  function  Compress(S: State_Vectors.State_Vector)
    return Compressed_Vector;
  procedure Expand(
    V: in Compressed_Vector; S: out State_Vectors.State_Vector);

private
  -- Compressed vector constrains Byte_Array_Base
  --   using the subtypes in package Config_State
  type Compressed_Vector is
    record
      Process:  Byte_Array_Base(Config_State.Process_Size_Index) :=
                  Zero_Bytes(Config_State.Process_Size_Index);
      Variable: Byte_Array_Base(Config_State.Data_Size_Index) :=
                  Zero_Bytes(Config_State.Data_Size_Index);
      Inner:    Byte := 0;
      Fair:     Byte := 0;
      Atomic:   Byte := None;
    end record;
end Compress_Vectors;
