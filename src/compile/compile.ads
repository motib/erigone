-- Copyright 2009 by  Mordechai (Moti) Ben-Ari. See version.ads
package Compile is
  -- Compile a Promela program from the Input_File
  procedure Compile_File(
    Source_File_Name: in String; Automata_File_Name: in String);

  -- Compile an expression from an LTL formula
  function  Compile_Expression(E: String) return String;
  -- Get numbers after compiling LTL which might have a constant
  function Get_I_Tab return String;
end Compile;
