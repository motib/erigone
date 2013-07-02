-- Copyright 2008-12 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Characters.Latin_1, Ada.Integer_Text_IO;
with Ada.Strings.Maps.Constants;
with Byte_IO;
with Ada.Long_Integer_Text_IO;
package body Utilities is
  use Ada.Strings.Fixed;

  -- Within S, find "Parm=Value," and return Value as String
  function Extract(S: String; Parm: String) return String is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    return Head(S(I .. Index(S,",",I)-1), Global.Name'Length);
  end Extract;

  -- Within S, find "Parm=Value," and return Value as Byte
  function Extract(S: String; Parm: String) return Byte is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    return Byte'Mod(
      Integer'Value(Head(S(I .. Index(S,",",I)-1), Global.Name'Length)));
  end Extract;

  -- Within S, find "Parm=Value," and return Value as Integer
  function Extract(S: String; Parm: String) return Integer is
    I: Natural := Index(S, Parm & "=") + Parm'Length + 1;
  begin
    return Integer'Value(Head(S(I .. Index(S,",",I)-1), Global.Name'Length));
  end Extract;

  -- Within S, find "Parm={Value}" and extract parenthesized Value
  function Extract_Paren(
    S: String; Parm: String; Open: String := "{"; Close: String := "}")
      return String is
    I: Natural := Index(S, Parm & "=" & Open) + Parm'Length + 2;
    J: Natural := Index(S, Close, I) - 1;
  begin
    return S(I .. J);
  end Extract_Paren;

  -- Construct string with line number and statement number
  function Line_Statement(L: Byte; S: String) return String is
  begin
    return "line=" & Trim(Byte'Image(L)) &
           ",statement={" & Trim(S) & "}";
  end Line_Statement;

  -- Put for Long_Integer with default Width => 0
  -- Optional new line
  procedure Put(Item: in Long_Integer; New_Line: in Boolean := False) is
  begin
    Ada.Long_Integer_Text_IO.Put(Item, Width => 0);
    Ada.Text_IO.Put(",");
    if New_Line then Ada.Text_IO.New_Line; end if;
  end Put;

  -- Put for Integer with default Width => 0
  -- Optional new line
  procedure Put(Item: in Integer; New_Line: in Boolean := False) is
  begin
    Ada.Integer_Text_IO.Put(Item, Width => 0);
    Ada.Text_IO.Put(",");
    if New_Line then Ada.Text_IO.New_Line; end if;
  end Put;

  -- Put for Long_Integer with default Width => 0
  -- S is a string for the named association of the value: S=Item,
  -- Optional new line
  procedure Put(S:    in String;
                Item: in Long_Integer; New_Line: in Boolean := False) is
  begin
    Ada.Text_IO.Put(S);
    Put(Item, New_Line);
  end Put;

  -- Put for Integer with default Width => 0
  -- S is a string for the named association of the value: S=Item,
  -- Optional new line
  procedure Put(S:    in String;
                Item: in Integer; New_Line: in Boolean := False) is
  begin
    Ada.Text_IO.Put(S);
    Put(Item, New_Line);
  end Put;

  -- Put for Byte with default Width => 0
  -- Optional new line
  procedure Put(Item: in Byte;    New_Line: in Boolean := False) is
  begin
    Byte_IO.Put(Item, Width => 0);
    Ada.Text_IO.Put(",");
    if New_Line then Ada.Text_IO.New_Line; end if;
  end Put;

  -- Put for Byte with default Width => 0
  -- S is a string for the named association of the value: S=Item,
  -- Optional new line
  procedure Put(S:    in String;
                Item: in Byte; New_Line: in Boolean := False) is
  begin
    Ada.Text_IO.Put(S);
    Put(Item, New_Line);
  end Put;

  -- Put S=Item with Boolean value Item in lower case
  procedure Put(S: in String;
                Item: in Boolean; New_Line: in Boolean := False) is
  begin 
    Ada.Text_IO.Put(S & To_Lower(Boolean'Image(Item)) & ",");
    if New_Line then Ada.Text_IO.New_Line; end if;
  end Put;
end Utilities;
