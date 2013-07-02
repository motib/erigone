-- Copyright 2008-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
package body States is
  -- Variable name/value pairs
  type Values is
    record
      Ident: Name;
      Value: Name;
    end record;

  -- Data for the current state
  Process:   Name := Blanks;
  Line:      Name := Blanks;
  Statement: Name := Blanks;
  Value_Set: array(Natural range 0..Max_Variables) of Values;

  -- Number of variables
  Variables: Natural := 0;
  -- Line counter for title
  Lines:     Natural := 0;

  -- Print title in include variable names
  procedure Print_Title is
    use Ada.Text_IO;
  begin
    Put(
      Process_Title(1..Process_Width) & ' ' &
      Line_Title(1..Line_Width) & ' ' &
      Statement_Title(1..Statement_Width) & ' ');
    for I in 0..Variables-1 loop
      Put(Value_Set(I).Ident(1..Variable_Width) & ' ');
    end loop;
    New_Line;
  end Print_Title;

  -- Print state data
  procedure Print_State(With_Data: Boolean := True) is
    use Ada.Text_IO, Ada.Strings;
  begin
    -- Don't print if an excluded statement is a substring of Statement
    for I in 0..Count_Statements-1 loop
      if Index(Trim(Statement, Right), 
               Trim(Excluded_Statements(I), Right)) /= 0 then
        return;
      end if;
    end loop;
    -- Check if title line should be written
    Lines := Lines + 1;
    if Lines > Title_Repeat then
      New_Line;
      Print_Title;
      Lines := 1;
    end if;

    if With_Data then
      Put(
        Process(  1..Process_Width)   & ' ' &
        Line     (1..Line_Width)      & ' ' &
        Statement(1..Statement_Width) & ' ');
    else
      Put(String'(1..Process_Width+Line_Width+Statement_Width+3 => ' '));
    end if;
    for I in 0..Variables-1 loop
      Put(Value_Set(I).Value(1..Variable_Width) & ' ');
    end loop;
    New_Line;
  end Print_State;

  -- Within S, find "Parm={Value}" and extract parenthesized Value
  function Extract_Paren(
    S: String; Parm: String; Open: String := "{"; Close: String := "}")
      return String is
    I: Natural := Index(S, Parm & "=" & Open) + Parm'Length + 2;
    J: Natural := Index(S, Close, I) - 1;
  begin
    return Head(S(I .. J), Name'Length);
  end Extract_Paren;

  -- Within string S, find "Parm=Value," and return Value
  function Extract(S: String; Parm: String) return String is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    if S(I) = '{' then
      return Extract_Paren(S, Parm);
    else
      return Head(S(I .. Index(S,",",I)-1), Name'Length);
    end if;
  end Extract;

  -- From "...,name=identifier,...,initial=value,..." set
  --   variable identifier and value
  procedure Set_Variable(S: in String; Parm: in String := "name") is
    use Ada.Text_IO, Ada.Strings;
    Ident: Global.Name := Extract(S, Parm);
  begin
    if Parm = "index" then
      Ident := "channel" & Extract(S, Parm)(1..Global.Name'Length-7);
    end if;

    -- Don't set if an excluded variable is a substring of "name"
    for I in 0..Count_Variables-1 loop
      if Index(Trim(Ident, Right), 
               Trim(Excluded_Variables(I), Right)) /= 0 then
        return;
      end if;
    end loop;

    Value_Set(Variables).Ident := Ident;
    Variables := Variables + 1;
  end Set_Variable;

  -- From "process=proc,...,line=n,statement=s," extract state data
  procedure Next_Transition(S: in String) is
  begin
    Process   := Extract(S, "process");
    Line      := Extract(S, "line");
    Statement := Extract_Paren(S, "statement");
  end Next_Transition;

  -- From "next state=,...,id1=val1,..." extract values of variables
  procedure Next_State(S: in String) is
  begin
    for I in 0..Variables-1 loop
      Value_Set(I).Value :=
        Extract(S, Trim(Value_Set(I).Ident, Ada.Strings.Right));
    end loop;
  end Next_State;
end States;
