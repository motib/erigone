--
--        Steps - Display step count only
--       Copyright 2012 by Mordechai (Moti) Ben-Ari.
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
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
procedure Steps is
  Trace_File: File_Type;
  S, Save: String(1..256) := (others => ' ');
  L, Lsave, I1, ISave, I2: Natural;
begin
  Open(Trace_File, In_File, Argument(1));
  while not End_Of_File(Trace_File) loop
    Get_Line(Trace_File, S, L);
    I1 := Index(S, "-n");
    I2 := Index(S, "steps=");
    if Index(S, "erigone") /= 0 then
      if I1 /= 0 then
        ISave := I1+2;
      else
        ISave := Index(S(1..L-1), " ", L-1, Ada.Strings.Backward);
      end if;
      LSave := L;
      Save(ISave..LSave) := S(ISave..LSave);
    elsif I2 = 1 then
      Put_Line("seed=" & Save(ISave..LSave) & S(1..L-1));
    end if;
  end loop;
exception
  when Name_Error => 
    Put_Line("No such file " & Argument(1));
end Steps;
