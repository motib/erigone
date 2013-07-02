-- Copyright 2008-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Global; use Global;
package States is
  procedure Print_Title;
  procedure Print_State(With_Data: Boolean := True);
  procedure Set_Variable(S: in String; Parm: in String := "name");
  procedure Next_Transition(S: in String);
  procedure Next_State(S: in String);
  function  Extract(S: String; Parm: String) return String;
private
  -- Arrays of excluded variables and statements
  type Name_Array      is array(Natural range 0..Max_Variables) of Name;
  Excluded_Variables:  Name_Array;
  Excluded_Statements: Name_Array;
  Count_Variables:     Natural := 0;
  Count_Statements:    Natural := 0;
end States;
