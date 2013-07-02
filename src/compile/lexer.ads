-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Compiler_Global; use  Compiler_Global;
package Lexer is
  -- The current position in the token array
  Tok         : Natural;

  -- The current symbol
  --   if it is an identifier, Id is its name
  --   if it is an integer constant,
  --     Inum is its value or a pointer to the number table
  --   if it is a string, Str is a pointer to the string table
  Sy          : Symbol;      -- current symbol
  Id          : Alfa;        -- name of current identifier
  IDNum       : Integer;     -- index of identifer for preprocessor
  Inum        : Integer;     -- value of integer constant
  Str         : Integer;     -- index into string table

  -- Since two-symbol lookahead is sometimes needed,
  --   these variables contain values for the "next" symbol
  Next_Sy     : Symbol; 
  Next_Id     : Alfa;
  Next_IDNum  : Integer;
  Next_Inum   : Integer;
  Next_Str    : Integer;

  -- Communication with preprocessor to maintain eols and indentation
  EOL         : Boolean;
  Indent      : Natural;

  -- Initialize lexer package variables
  procedure Initialize(E: String);

  -- Buffer and line counter are encapsulated
  -- Used to set line and source code in a transition
  function  Get_Buffer       return String;
  function  Get_Buffer_Ptr   return Lines_Ptr;
  function  Get_Line_Counter return Integer;
  function  Get_LTL          return String;

  function Get_Keyword(S: Symbol) return Alfa;

  -- Display an error with line and column
  --   Next: use next line and column rather than current
  procedure Error (E: in String; Next: Boolean := False);

  -- Check if the current symbol is P
  --   If so, read the next symbol; in not, E is the error message
  procedure Check_Symbol(P: in Symbol; E: in String);

  -- Get the next symbol from the token array
  procedure In_Symbol;
  -- Get the next symbol from the input (for the preprocessor)
  procedure Get_Symbol;

  -- Check if a symbol is in a certain category
  function  Is_Separator        (Item : Symbol) return Boolean;
  function  Type_Begin_Sy       (Item : Symbol) return Boolean;
  function  Factor_Begin_Sy     (Item : Symbol) return Boolean;
  function  Statement_Begin_Sy  (Item : Symbol) return Boolean;
  function  Process_Begin_Sy    (Item : Symbol) return Boolean;
  function  Channel_Op_Begin_Sy (Item : Symbol) return Boolean;
end Lexer;
