with Ada.Text_IO; use Ada.Text_IO;
with ada.Unchecked_Conversion;
package body Global is

  function Four_Bytes_To_Integer is 
    new Ada.Unchecked_Conversion(Four_Bytes, Integer);
  function Integer_to_Four_Bytes is 
    new Ada.Unchecked_Conversion(Integer, Four_Bytes);

  function Bytes_To_Integer(I: Four_Bytes) return Integer is
  begin
    return Four_Bytes_To_Integer(I);
  end Bytes_To_Integer;

  function Integer_To_Bytes(I: Integer) return Four_Bytes is
  begin
    return Integer_to_Four_Bytes(I);
  end Integer_To_Bytes;
end Global;
