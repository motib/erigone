-- Copyright 2011-12 by  Mordechai (Moti) Ben-Ari. GNU GPL.
--
--  Utilities for string processing
--
with Ada.Strings.Fixed;
with Global; use Global;
package Utilities is
  -- Pad string S to a Name
  function Pad(
    S:     in String;
    Count: in Natural   := Name'Length;
    Pad:   in Character := Ada.Strings.Space)
     return Name renames Ada.Strings.Fixed.Head;

  -- Trim string Source with default Side Both
  function Trim(
    Source: in String; 
    Side:   Ada.Strings.Trim_End := Ada.Strings.Both) 
      return String renames Ada.Strings.Fixed.Trim;

  -- Convert to integer and trim
  function Trim_Int(I: Integer) return String;

  -- Within S, find "Parm=Value,",
  --   and return Value as String or Integer
  function Extract(S: String; Parm: String) return String;
  function Extract(S: String; Parm: String) return Integer;

  -- Within S, find "Parm={Value}" and extract parenthesized Value
  function Extract_Paren(
    S: String; Parm: String; Open: String := "{"; Close: String := "}")
      return String;
end Utilities;
