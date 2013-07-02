-- Copyright 2008 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Command_Line;
package body States.Arguments is
  -- Set array of names A of excluded variables or statements
  --   by parsing strings S of the form aaaa#bbbb#
  --   where # is the constant Separator
  --   Count is the number of components set in A
  procedure Set_Name_Array(
      S: in String; A: in out Name_Array; Count: in out Natural) is
    Separator: constant String := "#";
    I: Natural := S'First;
    J: Natural;
  begin
    loop
      J := Index(S, Separator, I);
      exit when J = 0;
      A(Count) := Head(S(I .. J-1), Name'Length);
      Count := Count + 1;
      I := J + 1;
    end loop;
  end Set_Name_Array;

  procedure Usage is
    use Ada.Text_IO;
    begin
      New_Line;
      Put_Line("Usage trace [-tn] [-pn] [-ln] [-sn] [-vn] [-xs] [-ms] filename (no extension)");
      Put_Line("      after executing: erigone -dcmop filename > filename.trc");
      New_Line;
      Put_Line("      -tn number of lines between titles");
      Put_Line("      -pn, -ln, -sn, -vn field widths:");
      Put_Line("        Process, Line, Statement, Variable");
      New_Line;
      Put_Line("      -xs, -ms are excluded variables and statements");
      Put_Line("        s is a string of the form aaaa#bbbb#cccc#");
    end Usage;

  procedure Get_Arguments is
    use Ada.Command_Line, Ada.Text_IO;
  begin
    Put_Line("Trace v" & Version & ", Copyright " & Year &
             " by Moti Ben-Ari, GNU GPL.");
    if Argument_Count = 0 then
      raise Argument_Error;
    end if;
    for I in 1..Argument_Count-1 loop
      declare
        A: String := Argument(I);
      begin
        if    A(1..2) = "-t" then
          Title_Repeat    := Positive'Value(A(3..A'Last));
        elsif A(1..2) = "-p" then
          Process_Width   := Positive'Value(A(3..A'Last));
        elsif A(1..2) = "-l" then
          Line_Width      := Positive'Value(A(3..A'Last));
        elsif A(1..2) = "-s" then
          Statement_Width := Positive'Value(A(3..A'Last));
        elsif A(1..2) = "-v" then
          Variable_Width  := Positive'Value(A(3..A'Last));
        elsif A(1..2) = "-x" then
          Set_Name_Array(A(3..A'Last), Excluded_Variables,  Count_Variables);
        elsif A(1..2) = "-m" then
          Set_Name_Array(A(3..A'Last), Excluded_Statements, Count_Statements);
        else
          raise Argument_Error;
        end if;
      exception
        when Constraint_Error => raise Argument_Error;
      end;
    end loop;
    File_Name := new String'(Argument(Argument_Count) & Trace_Extension);
    return;
  exception
    when Argument_Error =>
      Usage;
      raise;
  end Get_Arguments;
end States.Arguments;
