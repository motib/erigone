--
--        VMC - Visualization of Model Checking in Erigone
--       Copyright 2011-12 by Mordechai (Moti) Ben-Ari.
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
--  Generates dot files that visualize the model checking process
--
--  To run:
--    erigone -dehlmprs verif filename > filename.trc
--      where verif blank for simulation
--      or a verification mode: -s, -a, -f
--      together with -t if an LTL formula is sued
--    vmc filename
--    This creates a subdirectory with dot files filename-nnn.dot
--    Run dot on each file to generate png
--    In Windows, the batch command is:
--      for %%F in (%1-*.dot) do
--        \"program files"\graphviz\bin\dot -Tpng %%F > %%~nF.png
--
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Global; use Global;
with Model_Data, Run_Data;
procedure VMC is
begin
  Put_Line("VMC Version " & Version & " Copyright " & Year &
           " by Mordechai (Moti) Ben-Ari. GNU GPL.");
  if Argument_Count = 0 then
    Put_Line("Missing file name");
    return;
  end if;
  File_Root := new String'(Argument(1));
  Open(Trace_File, In_File, File_Root.all & Trace_Extension);
  Model_Data.Read_Model;
  if Model_Data.Simulation then
    Run_Data.Read_Simulation_Data;
  else
    Run_Data.Read_Verification_Data;
  end if;
  Close(Trace_File);
exception
    when Name_Error =>
      Put_Line("Can't find file " & File_Root.all & Trace_Extension);
end VMC;
