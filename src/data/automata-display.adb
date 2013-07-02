-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Compiler_Declarations, Options, Utilities;
package body Automata.Display is
  -- Put the list of accept states, if any
  procedure Put_Accept_States is
  begin
    if Accept_Count = 0 then return; end if;
    Ada.Text_IO.Put_Line("accept states start=,");
    for A in 0 .. Accept_Count - 1 loop
      Utilities.Put("process=", Accept_Table(A).Process);
      Utilities.Put("state=",   Accept_Table(A).State, New_Line => True);
    end loop;
    Ada.Text_IO.Put_Line("accept states end=,");
  end Put_Accept_States;

  -- Put a byte code array
  procedure Put_Byte_Code(
      Code_Size: in Byte; Code: access Byte_Code_Array) is
    use Ada.Text_IO;
  begin
    if Options.Display(Options.Byte_Codes) then
      Put("byte code=" );
      if Code_Size = 0 then
        Put(",");
      else
        Put("{");
        for I in Byte range 0 .. Code_Size-1 loop
          Put(
            Utilities.To_Lower(
              Compiler_Declarations.Opcode'Image(Code(I).Operator)) &
            Byte'Image(Code(I).Operand1) &
            Byte'Image(Code(I).Operand2) & ",");
        end loop;
        Put("},");
       end if;
     end if;
     New_Line;
   end Put_Byte_Code;

  -- Display a single transition
  procedure Put_One_Transition(S: in Transitions) is
    use Utilities;
  begin
    Put("source=", S.Source);
    Put("target=", S.Target);
    Put("atomic=", S.Atomic);
    Put("end=",    S.End_Label);
    Put("accept=", S.Accept_Label);
    Put("line=",   S.Line_Number);
    Ada.Text_IO.Put(
      "statement={" & Utilities.Trim(S.Statement.all) & "},");
    Put_Byte_Code(S.Code_Size, S.Byte_Code);
  end Put_One_Transition;

  -- Display one location
  procedure Put_One_Location(L: in Location_Type) is
  begin
    Ada.Text_IO.Put("process=" & 
      Utilities.Trim(Program(L.Process).Identifier) & ",");
    -- Utilities.Put("process number=", L.Process); 
    Put_One_Transition(Program(L.Process).Transition_List(L.Transition));
  end Put_One_Location;

  -- Display all locations in a record L
  -- Also display the process executing with Atomic set, if any
  procedure Put_All_Locations(
    L: in Location_Record;
    Atomic: in Global.Byte;
    Handshake: in Global.Byte) is
 begin
     Utilities.Put(L.Count);

     if L.Never_Index /= None then
       Utilities.Put("never=", L.Never_Index);
     end if;
     if Atomic /= None then 
       Utilities.Put("atomic=", Atomic);
     end if;
     if Handshake /= 0 then
       Utilities.Put("handshake=", Handshake);
     end if;
     Ada.Text_IO.New_Line;

     if L.Count /= 0 then
       for I in 0..L.Count-1 loop
         Put_One_Location(L.Location_Array(I));
       end loop;
     end if;
  end Put_All_Locations;

  -- Display the automata
  procedure Put_One_Process(P: in Byte) is
    use Ada.Text_IO, Utilities;
    Proc: Process_Type renames Program(P);
  begin
    Put("process="  & Trim(Proc.Identifier) &
        ",initial=", Proc.Initial_State);
    Put("activated=", Proc.Is_Active);
    Put("pid=", Proc.PID);
    Put("transitions=", Proc.Count, New_Line => True);
    for T in 0..Proc.Count-1 loop
      Put("number=", T);
      Put_One_Transition(Program(P).Transition_List(T));
    end loop;
  end Put_One_Process;

  -- Display the automata
  procedure Put_Automata is
    use Ada.Text_IO, Utilities;
  begin
    if not Options.Display(Options.Program) then return; end if;
    Put_Line("transitions start=,");
    Put("processes=", Processes, New_Line => True);

    for I in Byte range 0..Processes-1 loop
      Put_One_Process(I);
    end loop;
    Put_Line("transitions end=,");
    Put_Accept_States;
  end Put_Automata;
end Automata.Display;
