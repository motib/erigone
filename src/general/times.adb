-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Calendar, Ada.Text_IO;
with Options;
package body Times is
  Start_Time, Compile_Time, Execute_Time: Ada.Calendar.Time;

  package Duration_IO is new Ada.Text_IO.Fixed_IO(Duration);

  -- Rename Put with new format defaults
  procedure Put(Item : in Duration;
    Fore: in Ada.Text_IO.Field := 0;
    Aft:  in Ada.Text_IO.Field := 2;
    Exp:  in Ada.Text_IO.Field := 0)
      renames Duration_IO.Put;

  -- Time of start of program
  procedure Start is
  begin
    Start_Time := Ada.Calendar.Clock;
  end Start;

  -- Time of end of compilation
  procedure End_Compile is
  begin
    Compile_Time := Ada.Calendar.Clock;
  end End_Compile;

  -- Time of end of execution
  procedure End_Execute is
  begin
    Execute_Time := Ada.Calendar.Clock;
  end End_Execute;

  -- Print times depending on execution mode
  procedure Print_Times is
    use Ada.Calendar, Ada.Text_IO, Options;
  begin
    if not Display(Run) then return; end if;
    Put("times=,compilation=");
    Put(Compile_Time - Start_Time);
    Put(",");
    if Execution_Mode = Compile_Only then
      New_Line;
      return;
    end if;
    if Execution_Mode = Simulation then
      Put("simulation=");
    else 
      Put("verification=");
    end if;
    Put(Execute_Time - Compile_Time);
    Put_Line(",");
  end Print_Times;
end Times;
