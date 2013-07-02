-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Utilities;
with Config;
package body Compress_Vectors is
  -- Check that the process and variable data can fit
  --   into a compressed vector
  procedure Check_Sizes(Processes: in Byte; Data_Size: in Byte) is
  begin
    if Processes > Config_State.Process_Size_Index'Last+1 then
      raise Unexpected_Input 
        with "too many processes" &
             Byte'Image(Processes) & " >" &
             Byte'Image(Config_State.Process_Size_Index'Last+1);
    end if;
    if Data_Size > Config_State.Data_Size_Index'Last+1 then
      raise Unexpected_Input
        with "data size too large"  &
             Byte'Image(Data_Size) & " >" &
             Byte'Image(Config_State.Data_Size_Index'Last+1);
    end if;
  end Check_Sizes;

  -- Compress State_Vector
  function Compress(S: State_Vectors.State_Vector)
    return Compressed_Vector is
  begin
    return (S.Process(Config_State.Process_Size_Index),
            S.Variable(Config_State.Data_Size_Index),
            S.Inner,
            S.Fair,
            S.Atomic);
  end Compress;

  -- Expand Compressed_Vector
  procedure Expand(
    V: in Compressed_Vector; S: out State_Vectors.State_Vector) is
  begin
    S.Process(Config_State.Process_Size_Index) := V.Process;
    S.Variable(Config_State.Data_Size_Index)   := V.Variable;
    S.Inner  := V.Inner;
    S.Fair   := V.Fair;
    S.Atomic := V.Atomic;
  end Expand;
end Compress_Vectors;
