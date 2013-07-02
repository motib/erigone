-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Compiler_Declarations;
package Compiler_Global is
  -- Subtype for identifiers
  subtype Alfa   is String(1 .. 32);
  -- Subtype for the input line and strings
  subtype Lines  is String(1..128);
  type    Lines_Ptr is access String;
  -- Subtype for tokens in source for preprocessor
  subtype Token_Index is Natural range 0..4095;

  -- Subtype for transitions per process
  subtype Transition_Index is Integer range 0 .. 255;
  -- Subtype for symbol table
  subtype Table_Index      is Integer range 0 .. 63;
  -- Subtype for byte code table for each statement
  subtype Byte_Code_Index  is Integer range 0 .. 255;

  -- Array type for storing:
  --   alternatives in if/do, forward gotos and breaks
  --   operands for channels, arguments for printf
  -- Subtype is also used for the goto fix table in State
  subtype Field_Index      is Integer range 0..31;
  type    Field_Array_Type is array(Field_Index) of Integer;

  -- Files
  Aut                : Ada.Text_IO.File_Type; -- Output file
  Inp                : Ada.Text_IO.File_Type; -- Input file

  -- Counters
  Number_Counter     : Natural;   -- Number of integer constants
  String_Counter     : Natural;   -- Number of string constants
  Token_Counter      : Natural;   -- Number of tokens in preprocessor
  ID_Counter         : Natural;   -- Number of identifiers for preproc
  T                  : Integer;   -- Number of symbols
  Transition_Counter : Integer;   -- Number of transitions per process

  -- Indices
  Level              : Integer;   -- 0=global, 1=table index of a proc
  State_Number       : Integer;   -- State number
  Offset             : Integer;   -- Offset in the state vector
  Process_Number     : Integer;   -- Number of proctypes

  -- Flags for controlling code generation
  -- Compiling a global declaration
  -- Set in Process_Declaration and Compile, used in Emit
  Declaration        : Boolean;
  -- Does statement start with an array?
  -- Set in Assignment, used in Factor
  LHS_Array          : Boolean;
  -- Load address not value of variable for receive without eval
  -- Set in Channel_Statement, used in Factor
  Emit_Load_Address  : Boolean;
  -- For receive with copy, ensure that > is not considered a relation
  -- Set in Channel_Statement, used in Relationalexpression
  Is_Copy            : Boolean;
  -- For compiling an LTL expression from a string not a file
  -- Set in Compile_Expression, used in Next_Ch
  No_File            : Boolean;

  -- Byte code record type and array of record type
  type Byte_Code is
    record
      Operator : Compiler_Declarations.Opcode := 
                  Compiler_Declarations.Noop;
      Operand1 : Integer := 0;
      Operand2 : Integer := 0;
    end record;
  type Byte_Code_Array is array (Byte_Code_Index) of Byte_Code;

  -- Types for symbol table components
  type Objects is (Variable, Parameter, Process, Label, MType);

  type Types   is
    (No_Typ, Ints, Shorts, Chans, Mtypes, Arrays, Bytes, Bits);

  type Symbol is
    (null_sy, eof_sy, intcon_sy, strng_sy, remote_sy, ident_sy   , 

     -- Keep the following together and in order for preprocessor debug
     plus_sy     , minus_sy    , times_sy   , idiv_sy    , imod_sy    ,
     and_sy      , or_sy       , bitand_sy  , bitor_sy   , xor_sy     ,
     eql_sy      , neq_sy      , gtr_sy     , geq_sy     ,
     lss_sy      , leq_sy      , lparent_sy , rparent_sy , comma_sy   ,
     left_sh_sy  , right_sh_sy , arrow_sy   ,
     semicolon_sy, period_sy   , becomes_sy , colon_sy   ,
     question_sy , exclamation_sy           ,
     double_colon_sy , double_question_sy , double_exclamation_sy ,
     double_period_sy,
     lbrace_sy   , rbrace_sy   , lbracket_sy , rbracket_sy,
     inc_sy      , dec_sy      , 
     
     -- Keep the following together and in order for binary search
     define_sy   , nr_pr_sy    , pid_fun_sy , active_sy  , assert_sy   ,
     atomic_sy   , bit_sy      , bool_sy    , break_sy   , byte_sy     ,
     c_code_sy   , c_decl_sy   , c_expr_sy  , c_state_sy , c_track_sy  ,
     chan_sy     , d_step_sy   , do_sy      , else_sy    ,
     empty_sy    , enabled_sy  , eval_sy    ,
     false_sy    , fi_sy       , for_sy     , full_sy    , goto_sy     ,
     hidden_sy   , if_sy       , init_sy    , inline_sy  , int_sy      ,
     len_sy      , local_sy    , ltl_sy     , mtype_sy   ,
     nempty_sy   , never_sy    , nfull_sy   , notrace_sy , 
     np_sy       , od_sy       , of_sy      ,
     pc_value_sy , pid_typ_sy  , printf_sy  ,
     printm_sy   , priority_sy , proctype_sy, provided_sy,
     run_sy      , select_sy   , short_sy   , show_sy    , skip_sy     ,
     timeout_sy  , trace_sy    , true_sy    , typedef_sy ,
     unless_sy   , unsigned_sy , xr_sy      , xs_sy
    );

  -- Symbol table element
  type Tab_Rec is
    record
      Name      : Alfa    := (others => ' ');
                                          -- symbol name
      Obj       : Objects := Variable;    -- variable, process, ...
      Typ       : Types   := No_Typ;      -- byte, bit, ...
      Eltype    : Types   := No_Typ;      -- array element type
      Sz        : Integer := 1;           -- Size or element size
      Lev       : Integer := 0;           -- 0=global or process index
      Adr       : Integer := 0;           -- offset in the state vector
      Len       : Integer := 0;           -- length of an array
      Parms     : Field_Array_Type := (others => 0);
                                          -- indices of parameters
      Code_Size : Integer := 0;           -- initialization
      Byte_Code : access Byte_Code_Array; --   byte code and size
    end record;

  -- Symbol table
  Tab : array(Table_Index) of Tab_Rec;

  type Token_Rec is
    record
      Sy: Symbol    := null_sy;
      ID: Integer   := 0;
      LC: Natural   := 0;
      St: Lines_Ptr;
    end record;

  -- Table of tokens for preprocessing
  type Token_Array is array(Token_Index) of Token_Rec;
  Token_Tab: Token_Array;

  -- Identifier table for preprocessing
  ID_Tab: array(Table_Index) of Alfa;

  -- Number table
  I_Tab : array(Table_Index) of Integer;

  -- String table
  -- Use access type to save space but don't bother deallocating
  S_Tab : array(Table_Index) of access String;

  -- Transition type and table (same as in automata.ads)
  -- Use access types to save space but don't bother deallocating
  type Transitions is
    record
      Statement    : Lines_Ptr;
      Source       : Integer := 0;
      Target       : Integer := 0;
      Atomic       : Integer := 0;
      End_Label    : Integer := 0;
      Accept_Label : Integer := 0;
      Line_Number  : Integer := 0;
      Code_Size    : Integer := 0;
      Byte_Code    : access Byte_Code_Array;
    end record;
  T_Tab : array (Transition_Index) of Transitions;
end Compiler_Global;
