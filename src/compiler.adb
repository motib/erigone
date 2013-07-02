-- Copyright 2009 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Command_Line, Ada.Text_IO, Ada.Strings.Bounded;
with Compiler_Declarations;
procedure Compiler is
  use  Ada.Command_Line;
  Usage_Error: exception;

  package Names is new Ada.Strings.Bounded.Generic_Bounded_Length(64);
  use Names;
  Promela_File, Automata_File, Root: Bounded_String;
  Extension:    Natural;

  procedure Error is
  begin
    Ada.Text_IO.Put_Line("Usage: compiler Promela-file [Automata-file]");
    raise Usage_Error;
  end Error;

begin
  if Argument_Count < 1 then Error; end if;
  Promela_File := To_Bounded_String(Argument(1));
  Extension := Index(Promela_File, ".");
  if Extension = 0 then
    Root := Promela_File;
    Promela_File := Promela_File & ".pml";
  else
    Root := Bounded_Slice(Promela_File, 1, Extension-1);
  end if;
  if Argument_Count = 1 then
    Automata_File := Root & ".aut";
  elsif Argument_Count = 2 then
    Automata_File := To_Bounded_String(Argument(2));
    if Index(Automata_File, ".") = 0 then
      Automata_File := Automata_file & ".aut";
    end if;
  else
    Error;
  end if;
  Compiler_Declarations.Compile_File(
    To_String(Promela_File), To_String(Automata_File));
end Compiler;
