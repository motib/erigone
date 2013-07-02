--
--        List - Erigone Compiler Listing with Bytecodes
--       Copyright 2011 by Mordechai (Moti) Ben-Ari.
-- 
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the GNU General Public License
-- as published by the Free Software Foundation; either version 2
-- of the License, or (at your option) any later version.
-- This program is distributed in the hope that it will be useful
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
-- See the GNU General Public License for more details.
-- You should have received a copy of the GNU General Public License
-- along with this program; if not, write to the Free Software
-- Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
-- 02111-1307, USA.
--
--
--  Print the transitions resulting from the compilation
--    together with the bytecodes
--  First execute: compiler filename or erigone -c filename
--  Reads the filename.aut and writes to filename.lst
--
with Ada.Text_IO;         use Ada.Text_IO;
with Ada.Integer_Text_IO; use Ada.Integer_Text_IO;
with Ada.Strings.Fixed;   use Ada.Strings.Fixed;
with Ada.Command_Line;    use Ada.Command_Line;
procedure List is
  Version:       constant String := "1.0";
  Year:          constant String := "2011";

  -- Files
  Automata_File: File_Type;
  List_File:     File_Type;

  -- String and length for Get_Line
  subtype        Line is String(1..2048);
  S:             Line;
  Length:        Natural;

  -- String subtypes for names and numbers
  subtype        Name   is String(1..8);
  subtype        Number is String(1..4);

  -- Within S, find "Parm=Value," and return Value as String
  function Extract(S: String; Parm: String) return String is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    return Head(S(I .. Index(S,",",I)-1), Name'Length);
  end Extract;

  -- Within S, find "Parm=Value," and return Value as Integer
  function Extract(S: String; Parm: String) return Integer is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    return
      Integer'Value(Head(S(I .. Index(S,",",I)-1), Number'Length));
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

  -- Put Integer with Width
  procedure PutW(Item: in Integer; W: in Integer := Number'Length) is
  begin
    Ada.Integer_Text_IO.Put(List_File, Item, Width => W);
  end PutW;

  -- Print a flag as a character or '-'
  procedure Print_Flag(
    Flag: in String; C1: in Character; C2: in Character := '-') is
  begin
    if Extract(S, Flag) = 1 then
      Put(List_File, C1);
    else
      Put(List_File, C2);
    end if;
  end Print_Flag;

  -- Print byte codes
  procedure Print_Byte_Codes(Indent: in Positive) is
    B: String := Extract_Paren(S, "byte code");
    Start: Positive := B'First;
  begin
    while Start < B'Last loop
      Put_Line(List_File,
        (1..Indent => ' ') & B(Start..Index(B,",", Start)-1));
        Start := Index(B,",", Start) + 1;
    end loop;
  end Print_Byte_Codes;
  
  -- Put symbol and constants
  procedure Print_Symbols_And_Constants is
    Start_Constants: Boolean := True;
    N1, N2:          Name;
  begin
    Put_Line(List_File, "Symbol  Type    Element SP  Off Len  Sz");

    loop
      exit when End_Of_File(Automata_File);
      Get_Line(Automata_File, S, Length);

      -- Print symbol name, type and element type if array
      if S(1..8) = "symbol=," then
        N1 := Extract(S, "type");
        if N1(1..5) = "array" then
          N2 := Extract(S, "element_type");
        else
          N2 := ('_', others => ' ');
        end if;
        Ada.Text_IO.Put(List_File,
          Extract(S, "name")      &
          Head(N1(1..Index(N1, "_")-1), Name'Length) &
          Head(N2(1..Index(N2, "_")-1), Name'Length)
        );

        -- Print scope and parameter
        Print_Flag("scope",     'L', 'G');
        Print_Flag("parameter", 'P');

        -- Print offset, length, size
        PutW(Extract(S, "offset"));
        PutW(Extract(S, "length"));
        PutW(Extract(S, "size"));
        New_Line(List_File);

        Print_Byte_Codes(29);

      -- Channel
      elsif S(1..8) = "channel=" then
        PutW(Extract(S, "name"));
        Ada.Text_IO.Put(List_File,
          (1..Name'Length - Number'Length => ' '));
        Ada.Text_IO.Put(List_File, Head("channel", Name'Length));
        declare
          T: String := Extract_Paren(S, "element_type");
          I: Positive := T'First;
          J: Natural := Index(T, "_", I);
        begin
          while Index(T, "_", I) /= 0 loop
            Ada.Text_IO.Put(List_File, T(I..Index(T, "_", I)-1) & ",");
            I := Index(T, ",", I) + 1;
          end loop;
        end;
        Ada.Text_IO.Put_Line(List_File,
          "    " & Extract_Paren(S, "element_size"));
        Ada.Text_IO.Put(List_File, (1..26 => ' '));
        PutW(Extract(S, "offset"));
        PutW(Extract(S, "length"));
        PutW(Extract(S, "size"));
        New_Line(List_File);

      -- Constant numbers and strings: offset and value
      elsif S(1..8) = "number=," or S(1..8) = "string=," then
        if Start_Constants then
          New_Line(List_File);
          Start_Constants := False;
        end if;
        Put(List_File, "Offset = ");
        PutW(Extract(S, "offset")); 
        Put(List_File, "   Value = ");
        Ada.Text_IO.Put(List_File, Extract(S, "value"));
        New_Line(List_File);

      -- Global variables
      elsif S(1..17) = "global_variables=" then
        Put(List_File, "Global variables = ");
        PutW(Extract(S, "global_variables"), 3);
        New_Line(List_File);
        New_Line(List_File);

      -- Local variables
      elsif S(1..8) = "process=" then
        Put(List_File, "Local variables = ");
        PutW(Extract(S, "local_variables"), 3);
        New_Line(List_File);
      end if;
    end loop;
  end Print_Symbols_And_Constants;

  -- Print processes
  procedure Print_Processes is

    -- Print transitions for a process
    procedure Put_Transitions(Count: in Positive) is
    begin
      Put_Line(List_File, " Src Tar   AEA  Line   Statement");

      for I in 1..Count loop
        Get_Line(Automata_File, S, Length);

        -- Print source and target states
        PutW(Extract(S, "source"));
        PutW(Extract(S, "target"));
        Ada.Text_IO.Put(List_File, "   ");

        -- Print flags
        Print_Flag("atomic", 'A');
        Print_Flag("end",    'E');
        Print_Flag("accept", 'A');

        -- Print line number and statement source code
        Ada.Text_IO.Put(List_File, "  ");
        PutW(Extract(S, "line"));
        Ada.Text_IO.Put(List_File, "   ");
        Ada.Text_IO.Put_Line(List_File, Extract_Paren(S, "statement"));

        Print_Byte_Codes(25);
      end loop;    
    end Put_Transitions;  

  begin  
    loop
      exit when End_Of_File(Automata_File);
      Get_Line(Automata_File, S, Length);
      if S(1..8) = "process=" then
        -- Print process data
        New_Line(List_File);
        Put(List_File, "Process = " & Extract(S, "process"));
        Put(List_File, "Actv = ");
        PutW(Extract(S, "active"), 2);
        Put(List_File, "  Init = ");
        PutW(Extract(S, "initial"), 2);
        Put(List_File, "  Trans = ");
        PutW(Extract(S, "transitions"), 3);
        New_Line(List_File);

        Put_Transitions(Extract(S, "transitions"));
      end if;
    end loop;
  end Print_Processes;

begin
  if Argument_Count = 0 then
    Put_Line("Missing filename");
    return;
  end if;

  declare
    A: String := Argument(1);
  begin
    Open(Automata_File, In_File,  A & ".aut");
    Create(List_File,   Out_File, A & ".lst");
  end;
  Put_Line(List_File, "List v" & Version & ", Copyright " & Year &
           " by Moti Ben-Ari, GNU GPL.");
  New_Line(List_File);

  Print_Symbols_And_Constants;
  Reset(Automata_File);
  Print_Processes;
exception
  when Name_Error => Put_Line("No such file");
end List;
