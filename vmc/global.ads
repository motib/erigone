-- Copyright 2011-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Ada.Strings.Fixed, Ada.Text_IO;
package Global is
  Version:         constant String  := "1.2";
  Year:            constant String  := "2011-12";
  DEBUG:           constant Boolean := False;

  -- Indices for tables of processes, variables, states, transitions
  --   Edge refers to the transitions of the state space so as to
  --     avoid confusion with the transitions of the model
  subtype Process_Index    is Natural range 0..7;
  subtype Variable_Index   is Natural range 0..15;
  subtype State_Index      is Natural range 0..255;
  subtype Transition_Index is Natural range 0..255;
  subtype Edge_Index       is Natural range 0..255;

  -- Fixed string for names and lines
  subtype Name is String(1..64);
  subtype Line is String(1..256);
  Blanks:      constant Name  := (others => ' ');

  -- File root name, files and file extensions 
  Trace_File:         Ada.Text_IO.File_Type;
  Dot_File:           Ada.Text_IO.File_Type;
  Prologue_File:      Ada.Text_IO.File_Type;
  File_Root:          access   String;
  Trace_Extension:    constant String := ".trc";
  Dot_Extension:      constant String := ".dot";
  Prologue_Extension: constant String := ".prg";

  -- Default dot prologue
  Prologue: constant array(0..2) of String(1..50) := (
      "  graph [size=""16,12"",ranksep=.25];               ",
      "  node [shape=box,fontname=Helvetica,fontsize=12];",
      "  node [width=1.6,height=1.2,fixedsize=true];     "
    );

  -- Effects on graphs
  Matched_Effect: constant String := " peripheries = 2 ";
  Current_Effect: constant String := " shape = ellipse ";
  Stack_Effect:   constant String := " style = bold ";
  Error_Effect:   constant String := " color = red ";
  Inner_Effect:   constant String := " style = filled ";
  End_Effect:     constant String := " #";
  Accept_Effect:  constant String := " *";
  Exec_Effect:    constant String := " @";
end Global;
