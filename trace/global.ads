-- Copyright 2008-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Ada.Strings.Fixed;
package Global is
  Version:         constant String := "1.2.1";
  Year:            constant String := "2008-12";

  Trace_Extension: constant String := ".trc";
  Max_Variables:   constant Positive := 100;

  subtype Name is String(1..64);
  subtype Line is String(1..256);
  Blanks:      constant Name  := (others => ' ');

  -- Widths of fields in table
  Process_Width:   Positive := 4;
  Line_Width:      Positive := 4;
  Statement_Width: Positive := 16;
  Variable_Width:  Positive := 8;
  
  -- Repeat title every n lines
  Title_Repeat:    Positive := 12;

  -- Title strings
  Process_Title:   Name := Ada.Strings.Fixed.Head("Process",   Name'Length);
  Line_Title:      Name := Ada.Strings.Fixed.Head("Line",      Name'Length);
  Statement_Title: Name := Ada.Strings.Fixed.Head("Statement", Name'Length);
end Global;
