-- Copyright 2011-12 by  Mordechai (Moti) Ben-Ari. GNU GPL.
--
--  Utilities for string processing
--
package body Utilities is
  use Ada.Strings.Fixed;

  -- Convert to integer and trim
  function Trim_Int(I: Integer) return String is
  begin
    return Trim(Integer'Image(I));
  end Trim_Int;

  -- Within S, find "Parm=Value," and return Value as String
  function Extract(S: String; Parm: String) return String is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    return Head(S(I .. Index(S,",",I)-1), Global.Name'Length);
  end Extract;

  -- Within S, find "Parm=Value," and return Value as Integer
  function Extract(S: String; Parm: String) return Integer is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    return Integer'Value(Head(S(I .. Index(S,",",I)-1), Global.Name'Length));
  end Extract;

  -- Within S, find "Parm={Value}" and extract parenthesized Value
  function Extract_Paren(
    S: String; Parm: String; Open: String := "{"; Close: String := "}")
      return String is
    I: Natural := Index(S, Parm & "=" & Open) + Parm'Length + 2;
    J: Natural := Index(S, Close, I) - 1;
  begin
    return S(I .. J);
  end Extract_Paren;
end Utilities;
