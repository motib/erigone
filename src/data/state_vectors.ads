-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
-- State vectors
--
with Config;
with Global; use Global;
package State_Vectors is
  -- A state vector contains:
  --   the current location counter of each process,
  --   the current value of each variable initialized to zero,
  --   a flag if in an inner search for an acceptance cycle,
  --   a counter for the fairness copies.
  type State_Vector is
    record
      Process:  Byte_Array_Base(Config.Process_Index) :=
                  Zero_Bytes(Config.Process_Index);
      Variable: Byte_Array_Base(Config.Data_Index)  := 
                  Zero_Bytes(Config.Data_Index);
      Inner:    Byte       := 0;
      Fair:     Byte       := 0;
      Atomic:   Byte       := None;
    end record;

  -- For zeroing a state vector
  Zero_Vector: constant State_Vector := 
    (Zero_Bytes(Config.Process_Index),  
     Zero_Bytes(Config.Data_Index), 0, 0, None);

 
  -- Get initial values for state vector
  function Get_Initial_State_Vector return State_Vector;


  -- Return the value of the location counter of Process from state vector S
  function Get_Process_Location_Value(
    S: State_Vector; Process: Byte) return Byte;

  -- Update the Value of a location counter in a Process in state vector S
  procedure Update_Process_Location(
    S:       in out State_Vector; 
    Process: in Byte; 
    Value:   in Byte);
  pragma Inline(Update_Process_Location);


  -- Return the value of a Variable from state vector S
  --   Functions for bytes, shorts and ints
  function Get_Byte_Variable_Value(
    S: State_Vector; Addr:    Byte) return Byte;
  pragma Inline(Get_Byte_Variable_Value);
  function Get_Short_Variable_Value(
    S:       State_Vector; Addr:    Byte) return Integer;
  pragma Inline(Get_Short_Variable_Value);
  function Get_Int_Variable_Value(
    S:       State_Vector; Addr:    Byte) return Integer;
  pragma Inline(Get_Int_Variable_Value);

  -- Function that calls the appropriate "Get" according to Size
  function Get_Variable_Value_By_Size(
    S:       State_Vector; 
    Addr:    Byte;
    Size:    Byte) return Integer;
  pragma Inline(Get_Variable_Value_By_Size);

  -- Get multiple bytes with one call 
  function Get_Variable_Value(
    S:       State_Vector; 
    Addr:    Byte;
    Size:    Byte) return Byte_Array_Base;
  pragma Inline(Get_Variable_Value);

  -- Update the Value of a Variable in the state vector S
  --   Procedures for bytes, shorts and ints
  procedure Update_Byte_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Byte);
  pragma Inline(Update_Byte_Variable);
  procedure Update_Short_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Integer);
  pragma Inline(Update_Short_Variable);
  procedure Update_Int_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Integer);
  pragma Inline(Update_Int_Variable);

  -- Procedure that calls the appropriate "Update" according to Size
  procedure Update_Variable_By_Size(
    S:        in out State_Vector;
    Addr:     in Byte;
    Size:     in Byte;
    Value:    in Integer);
  pragma Inline(Update_Variable_By_Size);

  -- Update multiple bytes (the Length of the array Value) with one call
  procedure Update_Variable(
    S:        in out State_Vector;
    Addr:     in Byte;
    Value:    in Byte_Array_Base);
  pragma Inline(Update_Variable);


  -- Put a prefix string P, followed by the state vector S
  procedure Put_State_Vector(P: in String; S: in State_Vector);
end State_Vectors;
