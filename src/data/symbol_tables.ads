-- Copyright 2008-11 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Symbol table
--
with Ada.Text_IO;
with Automata, Config;
with Global; use Global;
package Symbol_Tables is
  type Symbol_Type is
    (None, Bit_Type, Byte_Type, Short_Type, Int_Type,
     Proc_Type, MType_Type, Label_Type, Array_Type, Chan_Type);

  type Symbol is
    record
      Identifier:   Name        := Blanks;-- Symbol identifier
      Typ:          Symbol_Type := None;  -- Symbol type
      Parameter:    Byte        := 0;     -- Is it a parameter?
      Offset:       Byte        := 0;     -- Offset within state vector
      Element_Typ:  Symbol_Type := None;  -- Element of an array
      Size:         Byte        := 0;     -- Size or element size
      Length:       Byte        := 0;     -- Length of data in bytes
      Code_Size:    Byte        := 0;     -- Size of the byte code
      Scope:        Byte        := 0;     -- Global = 0, local = 1
      Byte_Code:    access Automata.Byte_Code_Array;
                                          -- Initialization byte code
    end record;

  -- Types and sizes of message elements for channels
  type Symbol_Array_Type is array(Config.Message_Index) of Symbol_Type;
  type Size_Array_Type   is array(Config.Message_Index) of Byte;

  type Channel is
    record
      Buffer_Size:    Byte := 0;   -- Buffer size (0 for rendezvous)
      Offset:         Byte := 0;   -- Offset of channel within state vector
      Length:         Byte := 0;   -- Size of channel within state vector
      Message_Length: Byte := 0;   -- Size of a single message
      Elements:       Byte := 0;   -- Number of elements in a message
      Element_Types:  Symbol_Array_Type := (others => None);
                                   -- Types of each element
      Element_Sizes:  Size_Array_Type   := (others => 0);
                                   -- Sizes of each element
    end record;

  -- Offset in the state vector of the start of the data for a process
  Frame_Starts: Byte_Array;
  Last_Frame:   Byte;
 
  -- Number of variables in the program
  Variables: Byte;

  -- Number of channels in the program
  Channels: Byte;

  -- Initialize library-level variables
  procedure Initialize;

  -- Get and set numbers, strings, mtypes, channels, symbols
  function  Get_Number (I: Byte) return Integer;
  function  Get_String (I: Byte) return String;
  function  Get_MType  (I: Byte) return String;
  function  Get_Channel(I: Byte) return Channel;
  function  Get_Symbol (I: Byte) return Symbol;

  procedure Set_Number (S: in String);
  procedure Set_String (S: in String);
  procedure Set_MType  (S: in String);
  procedure Set_Channel(S: in String);
  procedure Set_Symbol (S: in String);
  procedure Set_Global (S: in String);
  procedure Set_Local  (B: in Byte);

  -- Get the total size of the data to check size of state vector
  function  Get_Data_Size return Byte;

  -- Return an array of initial values of the variables
  --   by evaluating each initial expression.
  function  Get_Variable_Initials return Byte_Array_Base;

  -- Display the symbol table, the number table and the string table
  procedure Put_Symbol_Table;
  -- Put frame table is called for "active[N]" and "run"
  procedure Put_Frame_Table;
end Symbol_Tables;
