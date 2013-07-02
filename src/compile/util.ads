-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Strings.Fixed, Ada.Text_IO;
with Compiler_Declarations, Compiler_Global;
use  Compiler_Global;
package Util is
  -- Check if the capacity of a table has been exceeded
  procedure Check_Table(Value, Max: Integer; Name: String);

  -- Call Integer'Image and then Trim to remove the leading blank
  function  Trim_Int(N: Integer) return String;

  -- Ada.Strings.Fixed.Trim with default Side parameter
  function Trim(Source : in String;
                Side   : Ada.Strings.Trim_End := Ada.Strings.Both)
    return String renames Ada.Strings.Fixed.Trim;

  -- Pad renames Ada.Strings.Fixed.Head with spaces
  function Pad(S     : in String;
               Count : in Natural   := Alfa'Length;
               Pad   : in Character := Ada.Strings.Space)
    return Lines renames Ada.Strings.Fixed.Head;

  -- Put the tables to the "aut" file
  procedure Put_Numbers;
  procedure Put_Strings;
  procedure Put_Symbols;
  procedure Put_Transitions;

  -- Format a byte code
  function  Format_Code (B : in Byte_Code) return String;
  -- Format and put a byte code
  procedure Put_Byte_Code (B : in Byte_Code);

  -- Increment Transition_Counter, checking for table overflow
  procedure Increment_Transition_Counter;

  -- Enter an identifer into the symbol table
  procedure Enter(Id : in Alfa; K : in Objects);

  -- Search for an identifier in the symbol table
  --   Return index or zero if not found
  function  Loc(Id : in Alfa) return Integer;

  -- Emit a byte code into the byte code table
  --   of the current symbol or transition
  procedure Emit(
    Fct : in Compiler_Declarations.Opcode; A, B : in Integer);
end Util;
