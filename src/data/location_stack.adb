-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Automata.Display, Byte_IO, Files, Options, Utilities;
package body Location_Stack is
  -- The stack is an array of location items
  type Location_Array is array(Natural range <>) of Location_Item;

  Location_Stack: access Location_Array; -- Stack is allocated at runtime
  Top1:           Integer;               -- -1 for empty stack
  Max:            Natural;               -- Maximum number of elements used

  procedure Initialize is
  begin
    Location_Stack := new Location_Array(0..Options.Location_Stack_Max);
    Top1 := -1;
    Max  := 0;
  end Initialize;

  -- Put a location, optionally with the Flags
  --   Put the flags for the display but not in the trail file
  procedure Put_One_Location(S: in Location_Item; Flags: Boolean) is
  begin
    Utilities.Put("process=", S.L.Process);
    Utilities.Put("transition=", S.L.Transition);
    if Flags then
      Utilities.Put("never=", S.Never);
      Utilities.Put("visited=", S.Visited);
      Utilities.Put("last=", S.Last);
    end if;
    Ada.Text_IO.New_Line;
  end Put_One_Location;

  -- Display stack element with a Label for the stack operation
  procedure Display_Location(Label: in String; S: in Location_Item) is
  begin
    Utilities.Put(Label, Top1);
    Put_One_Location(S, Flags => True);
  end Display_Location;

  procedure Push(S: in Location_Item) is
  begin
    Top1 := Top1 + 1;
    if Top1 > Max then
      Max := Top1;
    end if;
    if Options.Display(Options.Location_Stack) then
      Display_Location("push transition=", S);
    end if;
    if Top1 > Location_Stack'Last then
      raise Global.Internal_Error with "location stack overflow";
    end if;
    Location_Stack(Top1) := S;
  end Push;

  procedure Pop is
  begin
    if Top1 < 0 then
      raise Global.Internal_Error with "location stack underflow";
    end if;
    if Options.Display(Options.Location_Stack) then
      Utilities.Put("pop transition=", Top1, New_Line => True);
    end if;
    Top1 := Top1 - 1;
  end Pop;

  function Top return Location_Item is
    S: Location_Item;
  begin
    S := Location_Stack(Top1);
    if Options.Display(Options.Location_Stack) then
      Display_Location("top transition=", S);
    end if;
    return S;
  exception
    when Constraint_Error =>
      raise Global.Internal_Error with "location stack underflow";
  end Top;

  function Empty return Boolean is
    B: Boolean := Top1 = -1;
  begin
    if B and then Options.Display(Options.Location_Stack) then
      Ada.Text_IO.Put_Line("empty location stack=,");
    end if;
    return B;
  end Empty;

  -- Set the Visited flag on the top element of the stack
  procedure Set_Visited is
  begin
    Location_Stack(Top1).Visited := True;
  end Set_Visited;

  -- Put statistics on the use of the stack
  procedure Put_Stack is
    use Utilities;
  begin
    Put("transition stack elements=", Max);
    Put("element size=", Integer'(Location_Item'Size/Global.Byte'Size));
    Put("memory=",
      Max*Location_Item'Size/Global.Byte'Size, New_Line => True);
  end Put_Stack;

  -- Write the trail from the location stack
  --   Error_Count is used for file name if writing all trails
  --   Start_Of_Acceptance_Cycle is the index of the stack element that
  --     starts the accept cycle (or -1)
  procedure Put_Trail(
      Error_Count:               in Positive;
      Start_Of_Acceptance_Cycle: in Integer;
      Never_Claim_Terminated:    in Boolean) is
    Trail_File: Ada.Text_IO.File_Type;
    L: Automata.Location_Type;
    use Ada.Text_IO;

    -- Null transitions should not be written to the trail  
    function Null_Transition return Boolean is
      T: Automata.Transitions :=
           Automata.Program(L.Process).Transition_List(L.Transition);
    begin
      return Utilities.Trim(T.Statement.all) = "null";
    end Null_Transition;
    
  begin
    if Top1 < 0 then return; end if;

    -- If writing all trails, use Root_File_Name to construct the file name
    if Options.Error_Number = 0 then
      Files.Trail_File_Name :=
        new String'(Files.Root_File_Name.all &
          Utilities.Trim(
            Integer'Image(Error_Count)) & Files.Trail_Extension);
    end if;

    Create(Trail_File, Out_File, Files.Trail_File_Name.all);

    if Options.Display(Options.Trail) then
      Put_Line("trail start=,");
      if Start_Of_Acceptance_Cycle /= -1 then
        Put_Line(
          "start of acceptance cycle=" &
          Utilities.Trim(Integer'Image(Start_Of_Acceptance_Cycle)) & ",");
      end if;
    end if;

    Put_Line(Trail_File,
      "start of acceptance cycle=" &
      Utilities.Trim(Integer'Image(Start_Of_Acceptance_Cycle)) & ",");

    -- A transition is in the trail if the visited flag is set
    for I in 0 .. Top1 loop
      L := Location_Stack(I).L;
      if Location_Stack(I).Visited and then not Null_Transition then
        -- Put the trail data to a file
        Put(Trail_File, "process=");
        Byte_IO.Put(Trail_File, L.Process, Width => 0);
        Put(Trail_File, ",transition=");
        Byte_IO.Put(Trail_File, L.Transition, Width => 0);
        Put_Line(Trail_File, ",");

        -- Display the trail data and the full transition data
        if Options.Display(Options.Trail) then
          Put_One_Location(Location_Stack(I), Flags => False);
          Automata.Display.Put_One_Location(L);
        end if;
      end if;
    end loop;
    if Start_Of_Acceptance_Cycle /= -1 then
      Put_Line(Trail_File, "end of acceptance cycle=,");
    end if;
    if Never_Claim_Terminated then
      Put_Line(Trail_File, "never claim terminated=,");
    end if;

    if Options.Display(Options.Trail) then
      if Start_Of_Acceptance_Cycle /= -1 then
        Put_Line("end of acceptance cycle=,");
      end if;
      if Never_Claim_Terminated then
        Put_Line("never claim terminated=,");
      end if;
      Put_Line("trail end=,");
    end if;
    Close(Trail_File);
  end Put_Trail;
end Location_Stack;
