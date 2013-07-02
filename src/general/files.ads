-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  File names and extensions
--
package Files is
  Source_Extension:   constant String := ".pml";
  LTL_Extension:      constant String := ".prp";
  Trail_Extension:    constant String := ".trl";
  Automata_Extension: constant String := ".aut";
  DOT_Extension:      constant String := ".dot";

  Root_File_Name:     access   String;
  Source_File_Name:   access   String;
  Trail_File_Name:    access   String;
  Automata_File_Name: access   String;
  DOT_File_Name:      access   String;

  LTL_File_Name:      access   String;
  LTL_Buffer:         access   String;  -- LTL buffer for inline formula
end Files;
