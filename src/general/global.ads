-- Copyright 2008-11 by  Mordechai (Moti) Ben-Ari. See version.ads
--
-- Compile-time types and constants
--
package Global is
  -- Byte is used for all indices and values of variables
  --   None used as null value
  type    Byte       is mod 256;
  for     Byte'Size  use 8;
  None:   constant   Byte := Byte'Last;

  -- Unconstrained Byte_Array_Base
  type        Byte_Array_Base is array(Byte range <>) of Byte;
  pragma      Pack(Byte_Array_Base);

  -- Constrained Byte_Array
  subtype     Byte_Array is Byte_Array_Base(Byte);
  Zero_Bytes: constant   Byte_Array := (others => 0);

  -- Process/variable names
  subtype Name           is String(1..32);
  Blanks: constant Name  := (others => ' ');

  -- Source statement
  subtype Line           is String(1..128);

  -- Exceptions
  --   Compilation_Error is declared in Compiler_Declarations
  File_Error:           exception;
  Internal_Error:       exception;
  Unexpected_Input:     exception;
  Termination_Error:    exception;
  Counterexample_Error: exception;

  -- Types and subprograms for bytes to/from integer
  subtype  Four_Bytes is Byte_Array_Base(0..3);
  function Integer_To_Bytes(I: Integer)    return Four_Bytes;
  function Bytes_To_Integer(I: Four_Bytes) return Integer;
end Global;
