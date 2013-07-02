-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
-- This package body is the only unit of the model checker
--   which "with"s the compiler: it renames its subprograms
with Compile;
package body Compiler_Declarations is
  procedure Compile_File(
    Source_File_Name: in String; Automata_File_Name: in String) 
    renames Compile.Compile_File;

  function Compile_Expression(Expression: String) return String
    renames Compile.Compile_Expression;
  function Get_I_Tab return String
    renames Compile.Get_I_Tab;
end Compiler_Declarations;
