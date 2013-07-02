-- Copyright 2011-12 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO; use Ada.Text_IO; with Ada.Strings.Fixed;
with Compiler_Declarations, Compiler_Global, Files, Global, Lexer, LTL;
with Options, Util, Utilities;
use  Compiler_Global, Lexer;
package body Preprocess is

  -- For each define or inline, store the name and tokens
  --   For inline, also store the formal parameters
  subtype Field_Index is Natural range 0..7;
  type Define_Record is
    record
      ID:          Natural;
      Parm_Count:  Natural := 0;
      Parms:       Token_Array;
      Token_Count: Natural := 0;
      Tokens:      Token_Array;
    end record;
  type Define_Array is array(Field_Index) of Define_Record;

  DA: Define_Array;
  D_Count: Natural;

  -- Delete Count components in Token_Tab, starting at From
  procedure Delete_Tokens(
    From:   in Token_Index;
    Count:  in Natural) is
  begin
    Token_Tab(From .. Token_Counter - Count) := 
      Token_Tab(From + Count .. Token_Counter);  
    Token_Counter := Token_Counter - Count;
  end Delete_Tokens;

  -- Add Count components from Source to Token_Tab starting at From
  procedure Add_Tokens(
    From:   in Token_Index;
    Source: in Token_Array; 
    Count:  in Natural) is
  begin
    Util.Check_Table(Token_Counter, Token_Tab'Last, "tokens");
    -- Make room for new tokens
    Token_Tab(From + Count .. Token_Counter + Count) :=
      Token_Tab(From .. Token_Counter);
    -- Insert the new tokens
    Token_Tab(From .. From + Count - 1) := 
      Source(Source'First .. Source'First + Count - 1);
    Token_Counter := Token_Counter + Count;
  end Add_Tokens;
    
  -- In the following procedures, I is the start of a construct
  --   and J continues on to the end of the construct
  -- Count is used to skip over "balanced" expressions or sequences
  --   When it is < 0, we have reached a right ) or } at the end
  --   of the construct
  -- LC is the line of the statement

  procedure Select_For_Statement(Sym: Symbol) is
    LC, I, J: Natural := 0;
    St:       Lines_Ptr;
    Count:    Integer;
    Var:      Token_Rec;     -- The variable of the statement
    TA:       Token_Array;   -- Construct the tokens before inserting
    TA_Count: Natural;
  begin
    while I < Token_Counter loop

      -- select or for statement
      if Token_Tab(I).Sy = Sym then
        TA_Count := 0;
        J := I + 1;
        if Token_Tab(J).Sy /= lparent_sy then Error("( expected"); end if;
        J := J + 1;

        -- Store variable that is defined and the "=" token
        LC := Token_Tab(J).LC;
        St := Token_Tab(J).St;
        Var := Token_Tab(J);
        TA(TA_Count) := Var;
        TA_Count := TA_Count + 1;
        TA(TA_Count) := (becomes_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;
        J := J + 1;
        if Token_Tab(J).Sy /= colon_sy then Error(": expected"); end if;
        J := J + 1;

        -- Lower bound expression
        while Token_Tab(J).Sy /= double_period_sy loop
          TA(TA_Count) := Token_Tab(J); 
          TA_Count := TA_Count + 1;
          J := J + 1;
        end loop;
        J := J + 1;

        -- Store "; do :: i <"
        TA(TA_Count) := (semicolon_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;
        TA(TA_Count) := (do_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;
        TA(TA_Count) := (double_colon_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;
        TA(TA_Count) := Var;
        TA_Count := TA_Count + 1;
        if Sym = select_sy then
          TA(TA_Count) := (lss_sy, 0, LC, St);
        else  -- for_sy
          TA(TA_Count) := (leq_sy, 0, LC, St);
        end if;
        TA_Count := TA_Count + 1;

        -- Upper bound expression
        Count := 0;
        loop
          if Token_Tab(J).Sy = lparent_sy then
            Count := Count + 1;
          elsif Token_Tab(J).Sy = rparent_sy then
            Count := Count - 1;
            exit when Count < 0;
          end if;
          TA(TA_Count) := Token_Tab(J); 
          TA_Count := TA_Count + 1;
          J := J + 1;
        end loop;
        J := J + 1;

        -- Store "-> sequence ;" 
        TA(TA_Count) := (arrow_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;

        if Sym = for_sy then
          if Token_Tab(J).Sy /= lbrace_sy then Error("{ expected"); end if;
          J := J + 1;
          LC := Token_Tab(J).LC;
          Count := 0;
          loop
            if Token_Tab(J).Sy = lbrace_sy then
              Count := Count + 1;
            elsif Token_Tab(J).Sy = rbrace_sy then
              Count := Count - 1;
              exit when Count < 0;
            end if;
            TA(TA_Count) := Token_Tab(J); 
            TA_Count := TA_Count + 1;
            J := J + 1;
          end loop;
          TA(TA_Count) := (semicolon_sy, 0, LC, St); 
          TA_Count := TA_Count + 1;
          J := J + 1;
        end if;

        -- Store i++ :: break od;"
        TA(TA_Count) := Var;
        TA(TA_Count).LC := LC;
        TA_Count := TA_Count + 1;
        TA(TA_Count) := (inc_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;
        TA(TA_Count) := (double_colon_sy, 0, LC, St);
        TA_Count := TA_Count + 1;
        TA(TA_Count) := (break_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;
        TA(TA_Count) := (od_sy, 0, LC, St); 
        TA_Count := TA_Count + 1;
        if Sym = for_sy then
          TA(TA_Count) := (semicolon_sy, 0, LC, St); 
          TA_Count := TA_Count + 1;
        end if;

        Delete_Tokens(I, J-I);
        Add_Tokens(I, TA, TA_Count);
        I := I + TA_Count;
      else
        I := I + 1;
      end if;

    end loop;
  end Select_For_Statement;

  -- Store define inline definitions in DA
  procedure Process_Inline(Is_Define: Boolean) is
    LC, I, J:  Natural := 0;
    Count: Integer := 0;
  begin
    while I < Token_Counter loop
      J := I + 1;

      -- Store inlines
      if (Is_Define     and Token_Tab(I).Sy = define_sy) or
         (not Is_Define and Token_Tab(I).Sy = inline_sy) then
        -- Identifier that is inlined
        DA(D_Count).ID := Token_Tab(J).ID;
        LC := Token_Tab(I).LC;
        J := J + 1;
        -- Opening parenthesis for paramters
        --   Distinguish between #define a(parms) and #define a ...
        if Token_Tab(J).Sy = lparent_sy and
            (not Is_Define or (Token_Tab(I).ID < 0)) then
          J := J + 1;
          -- Store formal parameters
          DA(D_Count).Parm_Count := 0;
          loop
            DA(D_Count).Parms(DA(D_Count).Parm_Count) := Token_Tab(J);
            DA(D_Count).Parm_Count := DA(D_Count).Parm_Count + 1;
            J := J + 1;
            exit when Token_Tab(J).Sy = rparent_sy;
            if Token_Tab(J).Sy /= comma_sy then Error(", expected"); end if;
            J := J + 1;
          end loop;
          J := J + 1;  -- skip over right parenthesis
        elsif not Is_Define then 
          Error("( expected");
        end if;

        -- Store tokens that define the inline
        if Token_Tab(J).Sy = lbrace_sy then
          if not Is_Define then
            J := J + 1;
          else
            Error("{ expected");
          end if;
        end if;
        DA(D_Count).Token_Count := 0;
        -- Since inlined code may have braces, assume they are
        --   balanced and copy tokens until extra right brace
        -- For define, exit at end of line
        loop
          if Is_Define then
            exit when Token_Tab(J).LC /= LC;
          else
            if Token_Tab(J).Sy = lbrace_sy then
              Count := Count + 1;
            elsif Token_Tab(J).Sy = rbrace_sy then
              Count := Count - 1;
              exit when Count < 0;
            end if;
          end if;
          DA(D_Count).Tokens(DA(D_Count).Token_Count) := Token_Tab(J);
          DA(D_Count).Token_Count := DA(D_Count).Token_Count + 1;
          J := J + 1;
        end loop;
        if not Is_Define then
          J := J + 1;  -- Skip over right brace
        end if;
        D_Count := D_Count + 1;
        Delete_Tokens(I, J-I);  -- Delete the inline definition
        J := I;
      end if;

      I := J;
    end loop;
  end Process_Inline;

  -- Expland an inline definition
  procedure Use_Inline(Is_Define: Boolean; Start_From: Natural := 0) is
    LC, J: Natural := 0;
    I: Natural := Start_From;
  begin
    while I < Token_Counter loop
      J := I + 1;

      -- For each identifier, check if it is the name of an inline
      if Token_Tab(I).Sy = ident_sy then
        for D in 0..D_Count-1 loop
          if DA(D).ID = Token_Tab(I).ID then

            -- Found an inline, get actual parameters
            if Token_Tab(J).Sy = lparent_sy then
              J := J + 1;
              declare
                Actuals: array(0..DA(D).Parm_Count-1) of Token_Array;
                A_Count: array(0..DA(D).Parm_Count-1) of Token_Index;
                K: Integer := 0;
              begin
                for P in 0 .. DA(D).Parm_Count-1 loop
                  -- Get tokens of each actual parameter
                  while Token_Tab(J+K).Sy /= comma_sy and
                        Token_Tab(J+K).Sy /= rparent_sy loop
                    K := K + 1;
                  end loop;
                  Actuals(P)(0..K-1) := Token_Tab(J..J+K-1);
                  A_Count(P) := K;
                  J := J + K + 1;                                
                end loop;

                -- Delete actual parameters
                Delete_Tokens(I, J-I);

                -- Replace inline call with tokens
                Add_Tokens(I, DA(D).Tokens, DA(D).Token_Count);
                J := I + DA(D).Token_Count;

                -- Replace formal parameters with actual parameters
                for L in I .. J loop
                  if Token_Tab(L).Sy = ident_sy then
                    for P in 0 .. DA(D).Parm_Count-1 loop
                      if Token_Tab(L).ID = DA(D).Parms(P).ID then
                        Delete_Tokens(L, 1);
                        for M in 0 .. A_Count(P)-1 loop
                          Actuals(P)(M).LC := Token_Tab(L).LC;
                        end loop;
                        Add_Tokens(L, Actuals(P), A_Count(P));
                        J := J + A_Count(P) - 1;
                      end if;
                    end loop;
                  end if;
                end loop;
                exit;
              end;
            else
              if Is_Define then   -- Define need not have parameters
                Delete_Tokens(I, 1);
                Add_Tokens(I, DA(D).Tokens, DA(D).Token_Count);
                J := I + DA(D).Token_Count;
              else   -- No parameters for define
                Error("( expected");
              end if;
            end if;  -- End of processing parameters
          end if;    -- Not this define
        end loop;  -- Try another define or inline
      end if;  -- This is not an identifier
      I := J;
    end loop;  -- Try another token
  end Use_Inline;

  -- Process embedded LTL specifications
  procedure LTL_Specs is
    Use_This_Spec: Boolean;
    use Options;
  begin
    -- For "-t-name", check if the identifier following "ltl" is "name"
    if next_sy = ident_sy then
      Use_This_Spec :=
        LTL_Mode = Internal and then
        Files.LTL_File_Name.all = Utilities.Trim(Next_ID);
      Get_Symbol;
    -- For "-t", use the specification if no identifier following "ltl"
    elsif LTL_Mode = Default_LTL then
      Use_This_Spec := True;
    end if;
    -- Get the LTL formula and if it is to be used,
    --   place its negation in LTL_Buffer
    declare
      S: String := Lexer.Get_LTL;
    begin
      if Use_This_Spec then
        Files.LTL_Buffer := new String'("!(" & S & ")");
      end if;
    end;
    while Sy = null_sy loop Get_Symbol; end loop;
  end LTL_Specs;

  Symbol_Reps: array(Symbol range plus_sy..dec_sy) of String(1..3) := (
      plus_sy    => "+  ", inc_sy      => "++ ", minus_sy   => "-  ",
      dec_sy     => "-- ", times_sy    => "*  ", idiv_sy    => "/  ",
      imod_sy    => "%  ", and_sy      => "&& ", or_sy      => "|| ",
      bitand_sy  => "&  ", bitor_sy    => "|  ", xor_sy     => "^  ",
      eql_sy     => "== ", neq_sy      => "!= ", gtr_sy     => ">  ",
      geq_sy     => ">= ", lss_sy      => "<  ", leq_sy     => "<= ",
      lparent_sy => "(  ", rparent_sy  => ")  ", comma_sy   => ",  ",
      left_sh_sy => "<< ", right_sh_sy => ">> ", arrow_sy   => "-> ",
      semicolon_sy => ";  ", period_sy    => ".  ",
      lbrace_sy    => "{  ", rbrace_sy    => "}  ",
      lbracket_sy  => "[  ", rbracket_sy  => "]  ",
      becomes_sy   => "=  ", colon_sy     => ":  ",
      exclamation_sy     => "!  ", double_colon_sy       => ":: ",
      double_question_sy => "?? ", double_exclamation_sy => "!! ",
      double_period_sy   => ".. ", question_sy           => "?  "
    );

  -- Print token array as source code
  procedure Put_Source is
    Previous_LC: Natural := 1;
  begin
    for I in 0..Token_Counter-1 loop
      -- When line number changes, output new line
      if Previous_LC /= Token_Tab(I).LC then
        New_Line;
        Previous_LC := Token_Tab(I).LC;
      end if;
      case Token_Tab(I).Sy is
         when define_sy .. xs_sy =>
           Put(Utilities.Trim(Get_Keyword(Token_Tab(I).Sy)) & " ");
         when intcon_sy          =>
           Put(Integer'Image(Token_Tab(I).ID));
         when strng_sy           =>
           Put('"' & S_Tab(Token_Tab(I).ID).all & '"');
         when ident_sy           =>
           Put(Utilities.Trim(ID_Tab(Token_Tab(I).ID)) & " ");
         when plus_sy..dec_sy    =>
           Put(Symbol_Reps(Token_Tab(I).Sy));
         when others             =>
           Put(Symbol'Image(Token_Tab(I).Sy) & " is not expected");
       end case;
    end loop;
    New_Line;
    Put_Line("-----------------------");
  end Put_Source;

  -- Read the source file and store the tokens in Token_Tab
  procedure Read_Tokens is
    Index: Integer;
  begin
    Get_Symbol;
    Get_Symbol;  -- Because of Next_Sy
    while Sy /= eof_sy loop
      if Sy = ltl_sy then
        LTL_Specs;
      else
        if    Sy = ident_sy  then Index := IDNum;
        elsif Sy = intcon_sy then Index := INum;
        elsif Sy = strng_sy  then Index := Str;
        elsif Sy = define_sy then Index := IDNum;
        else  Index := 0;
        end if;
        Util.Check_Table(Token_Counter, Token_Tab'Last, "tokens");
        Token_Tab(Token_Counter) :=
          (Sy, Index, Lexer.Get_Line_Counter, Lexer.Get_Buffer_Ptr);
        Token_Counter := Token_Counter + 1;
        Get_Symbol;
      end if;
    end loop;
  end Read_Tokens;
    
  -- Preprocess a Promela source code file
  procedure Preprocess_File is
    use type Options.LTL_Type;
  begin
    Read_Tokens;
    if Options.Debug(Options.Debug_Preprocessor) then Put_Source; end if;

    -- Check LTL mode
    --   If "-t-name" and "name" not found, this is an error
    if Options.LTL_Mode = Options.Internal and then
       Files.LTL_Buffer = null then
      raise Global.Unexpected_Input with
        "LTL specification """ & Files.LTL_File_Name.all &
        """ not found";
    -- If "-t" and no unnamed "ltl", "filename.prp" will be searched for
    elsif Options.LTL_Mode = Options.Default_LTL and then
       Files.LTL_Buffer = null then
      Put_Line("message=Unnamed internal LTL specification not found,");
      Put_LIne("message=Looking for file """ & Files.LTL_File_Name.all &
               """,");
    end if;

    D_Count := 0;

    Process_Inline(Is_Define => True);
    if D_Count > 0 then
      Use_Inline(Is_Define => True);
    end if;
    if Options.Debug(Options.Debug_Preprocessor) then Put_Source; end if;

    Process_Inline(Is_Define => False);
    if D_Count > 0 then
      Use_Inline(Is_Define => False);
    end if;
    if Options.Debug(Options.Debug_Preprocessor) then Put_Source; end if;

    Select_For_Statement(select_sy);
    if Options.Debug(Options.Debug_Preprocessor) then Put_Source; end if;

    Select_For_Statement(for_sy);
    if Options.Debug(Options.Debug_Preprocessor) then Put_Source; end if;
  end Preprocess_File;
end Preprocess;
