-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Compress_Vectors, Options, Utilities;
package body State_Stack is
  -- The stack is an array of compressed vectors
  type State_Array is array(Natural range <>) of 
    Compress_Vectors.Compressed_Vector;

  Stack: access State_Array;  -- The stack is allocated at runtime
  Top1:  Integer;             -- -1 for empty stack
  Max:   Natural;             -- Maximum number of elements used

  -- Check that the processes and data can fit
  --   into a compressed vector
  procedure Check_Sizes(
    Processes: in Global.Byte; Data_Size: in Global.Byte) is
  begin
    Compress_Vectors.Check_Sizes(Processes, Data_Size);
  end Check_Sizes;

  procedure Initialize is
  begin
    Stack := new State_Array(0..Options.State_Stack_Max);
    Top1  := -1;
    Max   := 0;
  end Initialize;

  -- Put statistics on the use of the stack
  procedure Put_Stack is
    S: Natural := Compress_Vectors.Compressed_Vector'Size;
    use Utilities;
  begin
    Put("state stack elements=", Max);
    Put("element size=", Integer'(S/Global.Byte'Size));
    Put("memory=", Max * S/Global.Byte'Size, New_Line => True);
  end Put_Stack;

  -- Display stack element with a Label for the stack operation
  procedure Display_Stack_Element(
    Label: in String; S: in State_Vectors.State_Vector) is
  begin
    Utilities.Put(Label, Top1);
    State_Vectors.Put_State_Vector("", S);
  end Display_Stack_Element;

  procedure Push(S: in State_Vectors.State_Vector) is
  begin
    Top1 := Top1 + 1;
    if Top1 > Max then
      Max := Top1;
    end if;
    if Top1 > Stack'Last then
      raise Global.Internal_Error with "state stack overflow";
    end if;
    if Options.Display(Options.State_Stack) then
      Display_Stack_Element("push state=", S);
    end if;
    Stack(Top1) := Compress_Vectors.Compress(S);
  end Push;

  procedure Pop(Reason: in Reason_Type) is
  begin
    if Top1 < 0 then
      raise Global.Internal_Error with "state stack underflow";
    end if;
    if Options.Display(Options.State_Stack) then
      Utilities.Put("pop state=", Top1);
      Ada.Text_IO.Put_Line(
        "reason=" & Utilities.To_Lower(Reason_Type'Image(Reason)) & ",");
    end if;
    Top1 := Top1 - 1;
  end Pop;

  function Top return State_Vectors.State_Vector is
    S: State_Vectors.State_Vector; 
  begin
    Compress_Vectors.Expand(Stack(Top1), S);
    if Options.Display(Options.State_Stack) then
      Display_Stack_Element("top state=", S);
    end if;
    return S;
  exception
    when Constraint_Error =>
      raise Global.Internal_Error with "state stack underflow";
  end Top;

  function Empty return Boolean is
    B: Boolean := Top1 = -1;
  begin
    if B and then Options.Display(Options.State_Stack) then
        Ada.Text_IO.Put_Line("empty state stack=,");
    end if;
    return B;
  end Empty;

  -- An acceptance cycle exists if a state S is already on the stack
  --   Returns the stack element or -1 if none
  -- S1 is S with Inner=0: we search for a state from the outer search
  function  On_Stack(S: in State_Vectors.State_Vector) return Integer is
    S1: State_Vectors.State_Vector := S;
    C: Compress_Vectors.Compressed_Vector;
    use type Compress_Vectors.Compressed_Vector;
  begin
    S1.Inner := 0;
    C := Compress_Vectors.Compress(S1);
    for I in reverse 0 .. Top1-1 loop   -- Search from Top of stack
      if C = Stack(I) then
        return I;
      end if;
    end loop;
    return -1;
  end On_Stack;

  -- Returns the matched element for printing
  function  Get_Element(I: in Integer) return State_Vectors.State_Vector is
    S: State_Vectors.State_Vector;
  begin
    Compress_Vectors.Expand(Stack(I), S);
    return S;
  end Get_Element;
end State_Stack;
