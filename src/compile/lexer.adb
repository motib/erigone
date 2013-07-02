-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO, Ada.Characters.Latin_1, Ada.Strings.Fixed;
with Compiler_Declarations, Options, Util;
use Util;
package body Lexer is

  -- Keywords must be in alphabetical order for binary search
  Key : constant array (Natural range <>) of Alfa := (
    Pad("#define"), Pad("_nr_pr")  , Pad("_pid")    , 
    Pad("active") , Pad("assert")  , Pad("atomic")  , Pad("bit")      ,
    Pad("bool")   , Pad("break")   , Pad("byte")    ,
    Pad("c_code") , Pad("c_decl")  , Pad("c_expr")  , Pad("c_state")  ,
    Pad("c_track"), Pad("chan")    ,
    Pad("d_step") , Pad("do")      , Pad("else")    , Pad("empty")    ,
    Pad("enabled"), Pad("eval")    , Pad("false")   , Pad("fi")       ,
    Pad("for")    ,
    Pad("full")   , Pad("goto")    , Pad("hidden")  , Pad("if")       ,
    Pad("init")   , Pad("inline")  , Pad("int")     ,
    Pad("len")    , Pad("local")   , Pad("ltl")     , 
    Pad("mtype")  , Pad("nempty")  , Pad("never")   , Pad("nfull")    ,
    Pad("notrace"), Pad("np_")     , Pad("od")      ,
    Pad("of")     , Pad("pc_value"), Pad("pid")     , Pad("printf")   ,
    Pad("printm") , Pad("priority"), Pad("proctype"), Pad("provided "),
    Pad("run")    ,
    Pad("select") , Pad("short")   , Pad("show")    , Pad("skip")    ,
    Pad("timeout"), Pad("trace")   , Pad("true")    , Pad("typedef")  ,
    Pad("unless") , Pad("unsigned"), Pad("xr")      , Pad("xs")
       );

  -- Input buffer and variables for reading from it
  Buffer       : Lines;       -- input buffer
  Buffer_Ptr   : Lines_Ptr;
  Next_Ptr     : Lines_Ptr;
  Ll           : Integer;     -- length of data in the input buffer
  Ch           : Character;   -- current character read
  Cc           : Integer;     -- input character counter
  Line_Counter : Integer;     -- input line counter
  Next_Cc      : Integer;
  Next_Lc      : Integer;

  function Get_Keyword(S: Symbol) return Alfa is
  begin
    if S in define_sy .. xs_sy then
      return Key(Symbol'Pos(S) - Symbol'Pos(define_sy));
    else
      return Alfa'(others => ' ');
    end if;
  end Get_Keyword;

  -- Initialize lexer package variables
  procedure Initialize(E: String) is
  begin
    Buffer(1..E'Length) := E;
    Ll            := E'Length;
    Ch            := ' ';
    Cc            := 0;
    Line_Counter  := 0;
    Next_Cc       := 0;
    Next_Lc       := 0;

    Sy            := null_sy;
    Next_Sy       := null_sy;
    EOL           := False;
    Indent        := 0;
  end Initialize;

  -- Buffer and line counter are encapsulated
  -- Used to set line and source code in a transition
  function  Get_Buffer return String is
  begin
    return Buffer(1..Ll);
  end Get_Buffer;

  function  Get_Buffer_Ptr return Lines_Ptr is
  begin
    return Buffer_Ptr;
  end Get_Buffer_Ptr;

  function Get_Line_Counter return Integer is
  begin
    return Line_Counter;
  end Get_Line_Counter;

  -- Display an error with line and column
  --   Next: use next line and column rather than current
  procedure Error (E: in String; Next: Boolean := False) is
    use Lexer;
  begin
    if Next then Line_Counter := Next_Lc; Cc := Next_Cc; end if;
    raise Compiler_Declarations.Compilation_Error
      with E & ":" & Trim_Int(Line_Counter) & ":" &
           Trim_Int(Cc) & ":" & Lexer.Buffer(1..Ll);
  end Error;

  -- Check if the current symbol is P
  --   If so, read the next symbol; in not, E is the error message
  procedure Check_Symbol(P: in Symbol; E: in String) is
  begin
    if Sy = P then In_Symbol; else Error(E & " expected"); end if;
  end Check_Symbol;

  -- Set next character in Ch, reading new lines as needed
  procedure Next_Ch is
    use Ada.Text_IO;
  begin
    if Next_Cc = Ll then  -- Read new line
      -- For compilation of LTL formula, there is only one line
      if No_File then
        Ch := Ada.Characters.Latin_1.ETX;
        return;
      end if;
      while End_Of_Line(Inp) and not End_Of_File(Inp) loop
        Skip_Line(Inp);
      end loop;
      if End_Of_File(Inp) then
        Ch := Ada.Characters.Latin_1.ETX;
        return;
      end if;
      Ll := 0;
      Next_Cc := 0;
      loop
        Get (Inp, Ch);
        Ll := Ll + 1;
        if Ch < ' ' then Ch := ' '; end if;
        Buffer(Ll) := Ch;
        exit when End_Of_Line (Inp);
      end loop;
      Ll         := Ll + 1;
      Buffer(Ll) := ' ';
      Buffer_Ptr := new String'(Buffer(1..Ll));
      -- Get actual line number to avoid problems with empty lines
      Next_Lc := Integer(Ada.Text_IO.Line(Inp));
      -- Set indent for preprocessor
      Indent := 1;
      while Buffer(Indent) = ' ' loop Indent := Indent + 1; end loop;
      If Indent > 1 then Indent := Indent - 1; end if;
      EOL := True;        -- End of line for preprocessor
    end if;
    Next_Cc := Next_Cc + 1;
    Ch := Buffer(Next_Cc);
  end Next_Ch;

  -- Put Next_Inum in the number table if it is not already there
  procedure Put_Num_In_Table is
  begin
    for I in 0 .. Number_Counter-1 loop
      if I_Tab (I) = Next_Inum then
        return;
      end if;
    end loop;
    Check_Table(Number_Counter, I_Tab'Last, "number");
    I_Tab (Number_Counter) := Next_Inum;
    Number_Counter         := Number_Counter + 1;
  end Put_Num_In_Table;

  -- Put Next_ID in the ID table if it is not already there
  procedure Put_ID_In_Table is
  begin
    for I in 0 .. ID_Counter-1 loop
      if ID_Tab (I) = Next_ID then
        Next_IDNum := I;
        return;
      end if;
    end loop;
    Check_Table(ID_Counter, ID_Tab'Last, "identifiers");
    ID_Tab (ID_Counter) := Next_ID;
    Next_IDNum          := ID_Counter;
    ID_Counter          := ID_Counter + 1;
  end Put_ID_In_Table;

  -- Put S in the string table if it is not already there
  procedure Put_String_In_Table(S: in String) is
  begin
    for I in 0 .. String_Counter-1 loop
      if S_Tab(I).all = S then
        Next_Str := I;
        return;
      end if;
    end loop;
    Check_Table(String_Counter, S_Tab'Last, "string");
    S_Tab(String_Counter) := new String'(S);
    Next_Str := String_Counter;
    String_Counter        := String_Counter + 1;
  end Put_String_In_Table;

  -- Get a symbol from the token array
  procedure In_Symbol is
    T: Token_Rec renames Token_Tab(Tok);
    use Ada.Text_IO;
  begin
    -- Copy "next" values and then read a new symbol into them
    Sy           := Next_Sy;
    Id           := Next_Id;
    IDNum        := Next_IDNum;
    Inum         := Next_Inum;
    Cc           := Next_Cc;
    Str          := Next_Str;
    Line_Counter := Next_Lc;
    Buffer_Ptr   := Next_Ptr;
    if Tok = Token_Counter then Next_Sy := eof_sy; return; end if;

    Next_Sy      := T.Sy;
    Line_Counter := T.LC;
    Next_Ptr     := T.St;
    if T.Sy = ident_sy then
      Next_ID    := ID_Tab(T.ID);
      if Ada.Strings.Fixed.Index(Next_ID, "@") /= 0 then
        Next_Sy  := remote_sy;
      end if;
    elsif T.Sy = intcon_sy then
      Next_INum := T.ID;
    elsif T.Sy = strng_sy then
      Next_Str  := T.ID;
    end if;
    Tok := Tok + 1;
    if Options.Debug(Options.Debug_Parser) then
      Put(Symbol'Image(Sy));
      if    Sy = intcon_sy then Put(Integer'Image(INum));
      elsif Sy = strng_sy  then Put('"' & S_Tab(Str).all & '"');
      elsif Sy = ident_sy  then Put(' ' & Id);
      end if;
      New_Line;
    end if;
  end In_Symbol;

  -- Get embedded LTL formula as a string
  function Get_LTL return String is
    K: Integer;
    S: Lines;
  begin
    K := 1;
    loop
      Next_Ch;
      exit when Ch = '}';
      S(K) := Ch;
      K := K + 1;
    end loop;
    Next_Ch;
    Sy           := null_sy;  -- Restart tokenizing
    Next_Sy      := null_sy;
    return S(1..K-1);
  end Get_LTL;

  -- Get a symbol from the input for the preprocessor
  procedure Get_Symbol is
    I, J, K  : Integer;
    S        : Lines;
  begin
    -- Copy "next" values and then read a new symbol into them
    Sy           := Next_Sy;
    Id           := Next_Id;
    IDNum        := Next_IDNum;
    Inum         := Next_Inum;
    Cc           := Next_Cc;
    Str          := Next_Str;
    Line_Counter := Next_Lc;

    <<L1>>
    -- Skip blanks
    while Ch = ' ' loop Next_Ch; end loop;

    case Ch is
      -- End of file
      when Ada.Characters.Latin_1.ETX => Next_Sy := eof_sy;

      -- Identifier or keyword
      when 'a' .. 'z' | 'A' .. 'Z' | '_' | '#' =>
        K  := 0;
        Next_Id := Pad(" ");
        loop
          K := K + 1;
          Next_Id(K) := Ch;
          Next_Ch;
          case Ch is
            when 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '#' | '@' => null;
            when others => exit;
          end case;
        end loop;

        -- Binary search for keywords
        I := Key'First;
        J := Key'Last;
        loop
          K := (I + J) / 2;
          if Next_Id <= Key (K) then J := K - 1; end if;
          if Next_Id >= Key (K) then I := K + 1; end if;
          exit when I > J;
        end loop;

        -- Found a keyword
        if I - 1 > J then
          Next_Sy := Symbol'Val(K + Symbol'Pos(define_sy));
        else  -- an identifer
          Next_Sy := ident_sy;
          -- Distinguish between macro with parameters and one
          --   whose definition starts with a parenthesis
          if Sy = define_sy and Ch = '(' then
            IDNum := -1;
          end if;
          Put_ID_In_Table;
        end if;

      -- Get a number and put into number table
      when '0' .. '9' =>
        Next_Sy   := intcon_sy;
        Next_Inum := 0;
        loop
          Next_Inum := Next_Inum*10 + Integer'Value(Ch&"");
          Next_Ch;
          exit when Ch not in '0' .. '9';
        end loop;
        Put_Num_In_Table;

      -- Comment /* ... */
      when '/' =>
        Next_Ch;
        if Ch = '*' then
          while Ch /= '/' loop
            loop Next_Ch; exit when Ch = '*'; end loop;
            Next_Ch;
          end loop;
          Next_Ch;
          goto L1;
        else
          Next_Sy := Idiv_sy;
        end if;

      -- Character 'x' is returned as its position
      when ''' =>
        Next_Ch;
        Next_Sy   := intcon_sy;
        Next_Inum := Character'Pos(Ch);
        Next_Ch;
        if Ch = ''' then Next_Ch;
        else Error("quote expected", Next => True);
        end if;
        Put_Num_In_Table;

      -- String "xxx"
      when '"' =>
        K := 1;
        loop
          Next_Ch;
          if Next_Cc = 1 then 
            Error("double quote expected", Next => True);
          end if;
          exit when Ch = '"';
          S(K) := Ch;
          K := K + 1;
        end loop;
        Next_Ch;
        Next_Sy := strng_sy;
        Put_String_In_Table(S(1..K-1));

      when '<' =>
        Next_Ch;
        if   Ch = '=' then Next_Sy := Leq_sy; Next_Ch;
        elsif Ch = '<' then Next_Sy := left_sh_sy; Next_Ch;
        else Next_Sy := Lss_sy;
        end if;

      when '>' =>
        Next_Ch;
        if Ch = '=' then Next_Sy := Geq_sy; Next_Ch;
        elsif Ch = '>' then Next_Sy := right_sh_sy; Next_Ch;
        else Next_Sy := Gtr_sy;
        end if;

      when '-' =>
        Next_Ch;
        if    Ch = '>' then Next_Sy := arrow_sy; Next_Ch;
        elsif Ch = '-' then Next_Sy := Dec_sy;       Next_Ch;
        else  Next_Sy := Minus_sy;
        end if;

      when '+' =>
        Next_Ch;
        if   Ch = '+' then Next_Sy := Inc_sy; Next_Ch;
        else Next_Sy := Plus_sy;
        end if;

      when '=' =>
        Next_Ch;
        if   Ch = '=' then Next_Sy := Eql_sy; Next_Ch;
        else Next_Sy := Becomes_sy;
        end if;

      when '.' =>
        Next_Ch;
        if   Ch = '.' then Next_Sy := double_period_sy; Next_Ch;
        else Next_Sy := Period_sy;
        end if;

      when '(' => Next_Sy := Lparent_sy;   Next_Ch;
      when '*' => Next_Sy := Times_sy;     Next_Ch;
      when '%' => Next_Sy := imod_sy;      Next_Ch;
      when '^' => Next_Sy := xor_sy;       Next_Ch;
      when ')' => Next_Sy := Rparent_sy;   Next_Ch;
      when ',' => Next_Sy := Comma_sy;     Next_Ch;
      when ';' => Next_Sy := Semicolon_sy; Next_Ch;
      when '{' => Next_Sy := Lbrace_sy;    Next_Ch;
      when '}' => Next_Sy := Rbrace_sy;    Next_Ch;
      when '[' => Next_Sy := Lbracket_sy;  Next_Ch;
      when ']' => Next_Sy := Rbracket_sy;  Next_Ch;

      when '?' =>
        Next_Ch;
        if   Ch = '?' then Next_Sy := double_question_sy; Next_Ch;
        else Next_Sy := Question_sy;
        end if;

      when '!' =>
        Next_Ch;
        if    Ch = '=' then Next_Sy := Neq_sy; Next_Ch;
        elsif Ch = '!' then Next_Sy := double_exclamation_sy; Next_Ch;
        else  Next_Sy := Exclamation_sy;
        end if;

      when '&' =>
        Next_Ch;
        if   Ch = '&' then Next_Sy := And_sy; Next_Ch;
        else Next_Sy := bitand_sy; Next_Ch;
        end if;

      when '|' =>
        Next_Ch;
        if   Ch = '|' then Next_Sy := Or_sy; Next_Ch;
        else Next_Sy := bitor_sy; Next_Ch;
        end if;

      when ':' =>
        Next_Ch;
        if    Ch = '=' then Next_Sy := Becomes_sy; Next_Ch;
        elsif Ch = ':' then Next_Sy := double_colon_sy; Next_Ch;
        else  Next_Sy := Colon_sy;
        end if;

      when others => Error("unrecognized symbol", Next => True);
    end case;
  end Get_Symbol;

  -- Check if a symbol is in a certain category

  function Is_Separator(Item: Symbol) return Boolean is
  begin
    return Item = semicolon_sy or Item = arrow_sy;
  end Is_Separator;
  
  function Type_Begin_Sy (Item : Symbol) return Boolean is
  begin
    case Item is
      when bit_sy    | bool_sy  | byte_sy  | pid_typ_sy | chan_sy |
           mtype_sy  | int_sy   | short_sy |
           hidden_sy | local_sy | xs_sy    | xr_sy =>
        return True;
      when others => return False;
    end case;
  end Type_Begin_Sy;

  function Factor_Begin_Sy (Item : Symbol) return Boolean is
  begin
    case Item is
      when intcon_sy | ident_sy | lparent_sy     | Lbracket_sy  |
           true_sy   | false_sy | exclamation_sy | pid_fun_sy   |
           len_sy    | empty_sy | nempty_sy      | full_sy      |
           nfull_sy  | nr_pr_sy | eval_sy        | remote_sy    =>
        return True;
      when others => return False;
    end case;
  end Factor_Begin_Sy;

  function Statement_Begin_Sy (Item : Symbol) return Boolean is
  begin
    case Item is
      when ident_sy  | if_sy     | do_sy     | assert_sy | goto_sy |
           printf_sy | atomic_sy | d_step_sy | run_sy    | skip_sy =>
        return True;
      when others => return False;
    end case;
  end Statement_Begin_Sy;

  function  Process_Begin_Sy (Item : Symbol) return Boolean is
  begin
    case Item is
      when active_sy | proctype_sy | init_sy => return True;
      when others => return False;
    end case;
  end Process_Begin_Sy;

  function Channel_Op_Begin_Sy (Item : Symbol) return Boolean is
  begin
    case Item is
      when question_sy    | double_question_sy    |
           exclamation_sy | double_exclamation_sy =>
        return True;
      when others => return False;
    end case;
  end Channel_Op_Begin_Sy;
end Lexer;
