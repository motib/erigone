--
--        Trace - Display trace of Erigone simulation
--       Copyright 2008-12 by Mordechai (Moti) Ben-Ari.
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
--  Print the trace of a simulation in table format
--  First execute: erigone -dcmp filename > filename.trc
--  This programs reads the trc file and prints the table
--
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Global, States.Arguments;
procedure Trace is
  Trace_File: File_Type;
  S:            Global.Line;      -- String and length for Get_Line
  Length:       Natural;

  -- Read lines until one is found containing the string T
  procedure Skip_Until(T1: in String; T2: in String := "") is
  begin
    loop
      Get_Line(Trace_File, S, Length);
      exit when Index(S, T1) /= 0;
      exit when T2 /= "" and then Index(S, T2) /= 0;
    end loop;
  end Skip_Until;

  -- Read pairs of chosen transition (for the process and statement),
  --   and next state (for the new values of the variables)
  -- The state is printed on the line of the _next_ transition
  procedure State_Loop is
    Acceptance:   Boolean := False; -- Start of acceptance cycle
  begin
    Skip_Until("initial state=");
    States.Next_State(S);
    loop
      Get_Line(Trace_File, S, Length);
      -- Start of acceptance cycle (-1 means none)
      if Index(S, "start of acceptance cycle") /= 0 then
        if Index(S, "start of acceptance cycle=-1,") = 0 then
          Acceptance := True;
        end if;
        -- Whatever the value, get the next line
        Get_Line(Trace_File, S, Length);
      end if;

      -- Get chosen transition
      exit when Index(S, "chosen transition=") /= 1;
      Get_Line(Trace_File, S, Length);   -- process=...
      States.Next_Transition(S);

      -- Skip over printf output: assume that Erigone output has final comma
      loop
        Get_Line(Trace_File, S, Length);
        exit when S(Length) = ',';
        Put_Line(S(1..Length));
      end loop;

      exit when Index(S, "next state=") /= 1;

      -- Print the values of the previous state
      States.Print_State;

      -- Print start of acceptance cycle here
      if Acceptance then
        Put_Line("start of acceptance cycle");
        Acceptance := False;
      end if;

      -- Parse values in next state
      States.Next_State(S);
    end loop;

    -- Print values of final state    
    States.Print_State(With_Data => False);
    Put_Line(S(1..Length));
  end State_Loop;

begin
  States.Arguments.Get_Arguments;
  Open(Trace_File, In_File, States.Arguments.File_Name.all);

  -- Set variable names from the symbol table data
  Skip_Until("symbol table start=");
  Get_Line(Trace_File, S, Length);
  loop
    Get_Line(Trace_File, S, Length);
    exit when Index(S, "symbol table end=") = 1;
    States.Set_Variable(S);
  end loop;

  -- Treat channels (if any) like variables
  Skip_Until("channel table start=", "data size=");
  if Index(S, "channel table start=") /= 0 then
    Get_Line(Trace_File, S, Length);
    loop
      Get_Line(Trace_File, S, Length);
      exit when Index(S, "channel table end=") = 1;
      if States.Extract(S, "buffer_size")(1..2) /= "0 " then
        States.Set_Variable(S, "index");
      end if;
    end loop;
  end if;

  States.Print_Title;
  State_Loop;
exception
  when Name_Error => 
    Put_Line("No such file " & States.Arguments.File_Name.all);
  when States.Arguments.Argument_Error =>
    null;
end Trace;
