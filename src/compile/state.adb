-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Compiler_Declarations, Compiler_Global, Expr, Lexer, Util;  
use  Compiler_Declarations, Compiler_Global, Lexer, Util;
package body State is
  -- Fix up forward goto's: the correct Target of Transition
  --   is the Adr field of Tab(Table_Index)
  type Goto_Fix is
    record
      Transition:  Integer;
      Table_Index: Integer;
    end record;
  Goto_Fixes  : array(Field_Index) of Goto_Fix;
  Fix_Counter : Integer;

  -- Fix up breaks. Table_Index is nesting level of do-od's
  Breaks      : array(Field_Index) of Goto_Fix;
  Break_Count : Integer;
  Do_Level    : Integer;    

  -- Index of current label
  Current_Label      : Integer;
  -- Atomic flag; set in Statement, used in Init_Transition
  Atomic             : Boolean;
  -- d_step flag; set in Statement, used in Init_Transition
  D_Step             : Boolean;

  procedure Initialize is
  begin
    Fix_Counter   := 0;
    Current_Label := 0;
    Break_Count   := 0;
    Do_Level      := 0;
    Atomic        := False;
    D_Step        := False;
  end Initialize;

  -- Initialize a new transition with source state S and target state T
  procedure Init_Transition (S, T : in Integer) is
    End_Label, Accept_Label, Atomic_Label : Integer := 0;
  begin
    -- Set end label
    if Current_Label /= 0 and then 
       Tab(Current_Label).Name(1..3) = "end" then
      End_Label := 1;
    end if;

    -- Set accept label
    if Current_Label /= 0 and then 
       Tab(Current_Label).Name(1..6) = "accept" then
      Accept_Label := 1;
    end if;

    -- Set atomic label
    if Atomic then Atomic_Label := 1; end if;
    if D_Step then Atomic_Label := 2; end if;

    -- Construct transition
    T_Tab (Transition_Counter) :=
     (Source       => S,
      Target       => T,
      Atomic       => Atomic_Label,
      End_Label    => End_Label,
      Accept_Label => Accept_Label,
      Line_Number  => Lexer.Get_Line_Counter,
      Statement    => Lexer.Get_Buffer_Ptr,
      Byte_Code    => new Byte_Code_Array'(others => <>),
      others => <>);
  end Init_Transition;

  -- Check for separating semicolon (unless fi, od, }, ::)
  procedure Check_Separator is
  begin
    if Sy = Semicolon_Sy or Sy = arrow_sy then
      In_Symbol;
    elsif Sy = fi_sy or Sy = od_sy or Sy = rbrace_sy or
          Sy = double_colon_sy then
      null;
    else
      Error("semicolon (or ->) expected");
    end if;
  end Check_Separator;

  -- Fix up forward gotos
  procedure Fix_Gotos is
  begin
    for F in 0..Fix_Counter-1 loop
      T_Tab(Goto_Fixes(F).Transition).Target :=
        Tab(Goto_Fixes(F).Table_Index).Adr;
    end loop;
  end Fix_Gotos;

  -- Emit store instruction depending on type
  procedure Store(I: in Integer; Is_Array: in Boolean) is
    Lv: Integer;
  begin
    if Tab(I).Lev > 0 then Lv := 1; else Lv := 0; end if;
    if I = 0 then -- Anonymous variable
      Emit(anon_store, 0, 0);
    elsif Is_Array then
      case Tab(I).Eltype is
        when Bits | Bytes | Chans | Mtypes =>
          Emit(byte_astore, Tab(I).Adr, Lv);
        when Shorts =>
          Emit(short_astore, Tab(I).Adr, Lv);
        when Ints =>
          Emit(int_astore, Tab(I).Adr, Lv);
        when others  => null;
      end case;
    else
      case Tab (I).Typ is
        when Bits | Bytes | MTypes | Chans =>
          Emit(byte_store, Tab(I).Adr, Lv);
        when Shorts =>
          Emit(short_store, Tab(I).Adr, Lv);
        when Ints =>
          Emit(int_store, Tab(I).Adr, Lv);
        when others => null;
      end case;
    end if;
  end Store;

  -- Emit load instruction depending on type
  procedure Load(I: in Integer; Is_Array: in Boolean) is
    Lv: Integer;
  begin
    if Tab(I).Lev > 0 then Lv := 1; else Lv := 0; end if;
    if Is_Array then
      case Tab(I).Eltype is
        when Bits | Bytes | Chans | Mtypes =>
          Emit(byte_aload, Tab(I).Adr, Lv);
        when Shorts =>
          Emit(short_aload, Tab(I).Adr, Lv);
        when Ints =>
          Emit(int_aload, Tab(I).Adr, Lv);
        when others  => null;
      end case;
    else
      case Tab (I).Typ is
        when Bits | Bytes | MTypes | Chans =>
          Emit(byte_load, Tab(I).Adr, Lv);
        when Shorts =>
          Emit(short_load, Tab(I).Adr, Lv);
        when Ints =>
          Emit(int_load, Tab(I).Adr, Lv);
        when others => null;
      end case;
    end if;
  end Load;
  
  procedure Statement is

    -- Compile if statement
    -- The source state of the first transition of all alternatives
    --   is the Source state of the "if"
    --   Save the transition indices in Firsts and fix up later
    -- The target state of the last transition of all alternatives
    --   is the state that follows the "fi"
    --   Save the transition indices in Lasts and fix up later
    procedure If_Statement is
      Source  : Integer := State_Number;
      Firsts  : Field_Array_Type;
      Lasts   : Field_Array_Type;
      Alt     : Integer := 0;           -- Number of alternatives
      Last_St : Symbol;                 -- Last symbol of an alternative
    begin
      In_Symbol;
      while Sy = double_colon_sy loop
        In_Symbol;
        Check_Table(Alt, Field_Index'Last, "if-fi fix");
        -- Remember the index of the first transition in an alternative
        Firsts(Alt) := Transition_Counter;

        -- Alternative contain statements, expressions or else
        while Statement_Begin_Sy (Sy) or Factor_Begin_Sy (Sy) or
              Sy = Break_Sy           or Sy = Else_Sy loop
          Last_St := Sy;  -- This might be the last symbol
          if Sy = Else_Sy then
            Init_Transition (Source, State_Number + 1);
            Emit(Logic_Else, 0, 0);
            State_Number  := State_Number + 1;
            Increment_Transition_Counter;
            In_Symbol;
            Check_Separator;
          elsif Sy = Break_Sy then
            -- Remember transition index of "break"
            Check_Table(Break_Count, Breaks'Last, "break fix");
            Breaks(Break_Count) := (Transition_Counter-1, Do_Level);
            Break_Count         := Break_Count + 1;
            In_Symbol;
            Check_Separator;
          else
            Statement;
          end if;
        end loop;

        -- Remember the index of the last transition in an alternative,
        --   but not if it is a goto, because it will be fixed up anyway
        if Last_St = goto_sy then Lasts(Alt) := -1;
        else                      Lasts(Alt) := Transition_Counter - 1;
        end if;
        Alt := Alt + 1;
      end loop;
      Check_Symbol(fi_sy, "fi");

      -- Fix up the first and last transitions of an alternative
      for T in 0 .. Alt - 1 loop
        T_Tab (Firsts (T)).Source := Source;
        if Lasts(T) /= -1 then  -- Not a goto
          T_Tab (Lasts (T)).Target := State_Number;
        end if;
      end loop;

      -- Make sure that there is a transition to jump to at the end
      Init_Transition (State_Number, State_Number + 1);
      Emit(noop, 0, 0);
      Increment_Transition_Counter;
      State_Number  := State_Number + 1;
    end If_Statement;

    -- Compile do statement
    -- The source state of the first transition of all alternatives
    --   is the Source state of the "do"
    --   Save the transition indices in Firsts and fix up later
    -- The target state of the last transition of all alternatives
    --   is the Source state of the "do"
    --   Save the transition indices in Lasts and fix up later
    -- Store transition indices of all "break" instructions in Breaks
    --   and fix up their targets with the state after the "od"
    -- Save the transition index of "do" in Start_Do (see below)
    procedure Do_Statement is
      Source      : Integer := State_Number;
      Start_Do    : Integer := Transition_Counter;
      Firsts      : Field_Array_Type;
      Lasts       : Field_Array_Type;
      Alt         : Integer := 0;   -- Number of alternatives
      Last_St     : Symbol;         -- Last symbol of an alternative
    begin
      Do_Level := Do_Level + 1;
      In_Symbol;
      while Sy = double_colon_sy loop
        In_Symbol;
        Check_Table(Alt, Field_Index'Last, "do-od fix");
        -- Remember index of first transition in an alternative
        Firsts(Alt) := Transition_Counter;

        -- If an alternative consists just of a break symbol,
        --   add a dummy transition: true -> break
        if Sy = Break_Sy then
          Init_Transition(State_Number, State_Number + 1);
          Emit(byte_push, 1, 0);  -- Dummy "true" expression
          Increment_Transition_Counter;
          State_Number  := State_Number + 1;
          Current_Label := 0;
        end if;

        -- Alternative contain statements, expressions, break or else
        while Statement_Begin_Sy (Sy) or Factor_Begin_Sy (Sy) or
              Sy = Break_Sy           or Sy = Else_Sy loop
          Last_St := Sy;
          if Sy = Break_Sy then
            -- Remember transition index of "break"
            Check_Table(Break_Count, Breaks'Last, "break fix");
            Breaks(Break_Count) := (Transition_Counter-1, Do_Level);
            Break_Count         := Break_Count + 1;
            In_Symbol;
            Check_Separator;
          elsif Sy = Else_Sy then
            Init_Transition (Source, State_Number + 1);
            Emit(Logic_Else, 0, 0);
            State_Number  := State_Number + 1;
            Increment_Transition_Counter;
            In_Symbol;
            Check_Separator;
          else
            Statement;
          end if;
        end loop;

        -- Remember the index of the last transition in an alternative,
        --   but not if it is a goto, because it will be fixed up anyway
        if Last_St = goto_sy then Lasts(Alt) := -1;
        else                      Lasts(Alt) := Transition_Counter - 1;
        end if;
        Alt := Alt + 1;
      end loop;
      Check_Symbol(od_sy, "od");

      -- Fix up the sources of the first and last transitions
      for A in 0 .. Alt - 1 loop
        T_Tab(Firsts(A)).Source := Source;
        if Lasts(A) /= -1 then
          T_Tab (Lasts (A)).Target := Source;
        end if;
      end loop;

      -- All transitions that jump to after "od" should jump to "do"
      --   For example, an "if" nested within a "do"
      for S in Start_Do .. Transition_Counter - 1 loop
        if T_Tab(S).Target = State_Number then
          T_Tab(S).Target := Source;
        end if;
      end loop;

      -- Fix up the targets of the "break" transitions
      while Break_Count > 0 and then
            Breaks(Break_Count-1).Table_Index = Do_Level loop
        T_Tab(Breaks(Break_Count-1).Transition).Target  := State_Number;
        Break_Count := Break_Count - 1;
      end loop;
      Do_Level := Do_Level - 1;
    end Do_Statement;

    -- For printf, channel, run statements, the operands are encountered
    --   in textual order: arg1, arg2, arg3, ...,
    --   but we want them pushed in reverse order: ..., arg3, arg2, arg1
    -- Reverse_Operands does this by copying the byte code array
    --   to a temporary variable and copying back field-by-field.
    -- Ops is the number of operands and Offsets is an array of the
    --   offsets of each operand within the byte code array
    procedure Reverse_Operands(
        Ops: in Integer; Offsets: in Field_Array_Type) is
      Temp: Byte_Code_Array := T_Tab(Transition_Counter).Byte_Code.all;
      From, To: Integer;
      Start: Integer := 0;
    begin
      for K in 0..Ops-1 loop
        From := Offsets(Ops-1-K);
        To   := Offsets(Ops-1-K+1)-1;
        T_Tab(Transition_Counter).Byte_Code(Start .. Start+To-From) :=
          Temp(From .. To);
        Start := Start + To-From+1;
      end loop;
    end Reverse_Operands;

    -- Compile "printf(format specifier, arg, arg, ...)
    procedure Printf is
      Offsets : Field_Array_Type := (others => 0);
      Args    : Integer := 0;
    begin
      In_Symbol;
      Check_Symbol(lparent_sy, "(");
      Check_Symbol(strng_sy,   "string");  -- Str has string table index
      -- Compile arguments
      while Sy = Comma_Sy loop
        In_Symbol;
        Expr.Expression;
        Args := Args + 1;
        Offsets(Args) := T_Tab(Transition_Counter).Code_Size;
      end loop;
      Reverse_Operands(Args, Offsets);
      Emit (Printf, Str, Args);
      Check_Symbol(rparent_sy, ")");
    end Printf;

    -- Compile a channel statement
    procedure Channel_Statement(I: in Integer; Is_Array: in Boolean) is
      Chan_Sy    : Symbol;       -- Remember channel operation symbol
      Chan_Mode  : Integer := 0; -- 0=move, 1=copy, 2=poll
      Offsets    : Field_Array_Type := (others => 0);
      Args       : Integer := 0;
      Arg_Offset : Integer := 0; -- For chan[n] there is already code
    begin
      if T_Tab(Transition_Counter).Code_Size > 0 then
        Arg_Offset := 1;
        Offsets(1) := T_Tab(Transition_Counter).Code_Size;
      end if;
      Chan_Sy := Sy;
      In_Symbol;
      -- <...> means copy, [...] means poll
      if    sy = lss_sy      then Chan_Mode := 1; In_Symbol;
      elsif sy = lbracket_sy then Chan_Mode := 2; In_Symbol;
      end if;
      Is_Copy := Chan_Mode = 1; -- Do not consider ">" an operator

      -- Compile all arguments
      while Factor_Begin_Sy(Sy) loop
        -- Set Emit_Load_Address flag:
        --   True  for receive without eval
        --   False for send or receive with eval
        if sy = eval_sy then
          In_Symbol;
          Check_Symbol(lparent_sy, "(");
          Emit_Load_Address := False;
        else
          Emit_Load_Address :=
            chan_sy /= exclamation_sy and 
            chan_sy /= double_exclamation_sy;
        end if;

        Expr.Expression;
        if sy = rparent_sy then In_Symbol; end if;
        Args := Args + 1;
        Offsets(Arg_Offset + Args) :=
          T_Tab(Transition_Counter).Code_Size;
        exit when sy /= comma_sy;
        In_Symbol;
      end loop;

      -- Skip over ">" or "]" for copy or poll
      if    Chan_Mode = 1 then Check_Symbol(gtr_sy, ">");
      elsif Chan_Mode = 2 then Check_Symbol(rbracket_sy, "]");
      end if;
      Reverse_Operands(Arg_Offset + Args, Offsets);
      -- Emit opcode for the index of the channel
      Load(I, Is_Array);

      -- Emit opcode depending on the symbol
      case Chan_Sy is
        when question_sy           =>
          if    Chan_Mode = 0 then Emit(move_fifo_receive, Args, 0);
          elsif Chan_Mode = 1 then Emit(copy_fifo_receive, Args, 0);
          else                     Emit(fifo_poll,         Args, 0);
          end if;
        when double_question_sy    =>
          if    Chan_Mode = 0 then Emit(move_random_receive, Args, 0);
          elsif Chan_Mode = 1 then Emit(copy_random_receive, Args, 0);
          else                     Emit(random_poll,         Args, 0);
          end if;
        when exclamation_sy        => Emit(fifo_send, Args, 0);
        when double_exclamation_sy => Emit(sorted_send, Args, 0);
        when others                => null;
      end case;
      Emit_Load_Address := False;
    end Channel_Statement;

    -- Compile "run process(arg, arg, ...)"
    --   The args are evaluated in reverse order,
    --   then the "run" instruction and then "store" instructions
    procedure Run is
      Offsets : Field_Array_Type := (others => 0);
      Args    : Integer := 0;
      I       : Integer;
    begin
      In_Symbol;
      Check_Symbol(ident_sy, "identifier");
      I := Loc(Id);
      if I = 0 then
        Error ("identifier " & Trim(Id) & " not declared");
      end if;
      Emit(run, Tab(I).Adr, 0);  -- Emit with the process counter
      Args := Args + 1;
      Offsets(Args) := T_Tab(Transition_Counter).Code_Size;

      Check_Symbol(lparent_sy, "(");
      if sy /= rparent_sy then   -- Compile actual arguments
        loop
          Expr.Expression;
          Args := Args + 1;
          Offsets(Args) := T_Tab(Transition_Counter).Code_Size;
          if    Sy = comma_sy   then In_Symbol;
          elsif Sy = rparent_sy then exit;
          else  Error(", or ) expected");
          end if;
        end loop;
      end if;
      Reverse_Operands(Args, Offsets);

      -- Emit "store" instructions for arguments
      for P in 0..Tab(I).Len-1 loop
        Store(Tab(I).Parms(P), False);
      end loop;
      Check_Symbol(rparent_sy, ")");
    end Run;

    -- Compile assignment statement
    procedure Assignment(I : in Integer) is
      Is_Array : Boolean := False;
    begin
      LHS_Array := False;
      -- Check for array selection
      if Sy = Lbracket_Sy then
        Is_Array  := True;
        Expr.Selector(I);
      end if;

      if    sy = inc_sy or sy = dec_sy then
        if Is_Array then
          -- Duplicate load of index for store
          declare
            TT: Transitions renames T_Tab(Transition_Counter);
          begin
            for K in 0 .. TT.Code_Size-1 loop
              TT.Byte_Code(TT.Code_Size + K) := TT.Byte_Code(K);
            end loop;
            TT.Code_Size := 2 * TT.Code_Size - 1;
          end;
        end if;
        Load(I, Is_Array);
        Emit(byte_push, 1, 0);
        if sy = inc_sy then
          Emit(iadd, 0, 0);
        else
          Emit(isub, 0, 0);
        end if;
        Store(I, Is_Array);
        In_Symbol;

      -- Compile the right hand side of an assignment statement
      elsif Sy = Becomes_Sy then
        In_Symbol;
        Expr.Expression;
        Store(I, Is_Array);

      -- Compile a channel statement
      elsif Channel_Op_Begin_Sy(Sy) then
        Channel_Statement(I, Is_Array);

      -- An expression statement like "a[n] >= b"
      else
        if Is_Array then
          Load(I, Is_Array);
          LHS_Array := True; -- The first Factor has been compiled
        end if;
        Expr.Expression;
      end if;
    end Assignment;

  I  : Integer;  -- Index to symbol table

  begin -- Statement
    -- Check first for label
    -- If first occurrence of a label, enter it in the symbol table
    --   Otherwise it occurred in a forward goto, set the state number
    if Sy = Ident_sy and Next_Sy = colon_sy then
      I := Loc(Id);
      if I = 0 then Enter(Id, Label);
      else          Tab(I).Adr := State_Number;
      end if;
      if I = 0 then
        -- Set for labels used in remote references in LTL formulas
        Tab(T).Adr := State_Number;
        Tab(T).Len := Process_Number;
      end if;
      Current_Label := T;
      In_Symbol;
      In_Symbol;
    end if;

    -- Statements that start with an identifier
    if Sy = Ident_Sy then
      if Next_Sy = LBracket_sy or Next_Sy = Becomes_Sy or
         Next_sy = Inc_Sy      or Next_sy = Dec_Sy     or
         Channel_Op_Begin_Sy(Next_Sy) then
        I := Loc(Id);
        if I = 0 and then Id /= Pad("_") then -- Anonymous variable 
          Error("identifier " & Trim(Id) & " not declared");
        end if;
        Init_Transition (State_Number, State_Number + 1);
        In_Symbol;
        Assignment(I);
        Increment_Transition_Counter;
        State_Number  := State_Number + 1;
        Current_Label := 0;

      else -- Statement that is an expression like "n==10"
        Init_Transition(State_Number, State_Number + 1);
        Expr.Expression;
        Increment_Transition_Counter;
        State_Number  := State_Number + 1;
        Current_Label := 0;
      end if;

    -- Compile compound statements
    elsif Sy = If_Sy then If_Statement;

    elsif Sy = Do_Sy then Do_Statement;

    elsif Sy = atomic_sy or Sy = d_step_sy then
      Atomic := sy = atomic_sy;
      D_Step := sy = d_step_sy;
      In_Symbol;
      Check_Symbol(lbrace_sy, "{");
      while sy /= rbrace_sy loop
        Statement;
      end loop;
      -- T_Tab(Transition_Counter-1).Atomic := 0;
      Atomic := False;
      D_Step := False;
      Check_Symbol(rbrace_sy, "}");
      -- In Spin, separator is optional although it is required by BNF
      -- Don't call Check_Separator, just check for ; or -> and return
      if Is_Separator(Sy) then In_Symbol; end if;
      return;

    -- Compile goto statements
    elsif Sy = goto_sy then
      In_Symbol;
      I := Loc(Id);
      if I /= 0 and then Tab(I).Adr /= -1 then
        -- The label was already encountered: set target of transition
        T_Tab (Transition_Counter-1).Target := Tab(I).Adr;
      else  -- A new label: enter in symbol table with Adr=-1
        if I = 0 then
          Enter(Id, Label);
          Tab(T).Adr := -1;
          I := T;
        end if;
        -- Fix goto later with indices in transition and symbol tables
        Check_Table(Fix_Counter, Goto_Fixes'Last, "goto");
        Goto_Fixes(Fix_Counter) := (Transition_Counter-1, I);
        Fix_Counter := Fix_Counter + 1;
      end if;
      In_Symbol;

    -- Compile other statements
    elsif Sy = assert_sy or Sy = printf_sy or Sy = run_sy or
          Sy = skip_sy   or Factor_Begin_Sy (Sy) then
      Init_Transition (State_Number, State_Number + 1);
      case Sy is
        when assert_sy =>
          In_Symbol;
          Expr.Expression;
          Emit (Assert, 0, 0);
        when run_sy    => Run;
        when printf_sy => Printf;
        when skip_sy   => Emit(noop, 0, 0); In_Symbol;
        when others    => Expr.Expression;
      end case;
      Increment_Transition_Counter;
      State_Number  := State_Number + 1;
      Current_Label := 0;
    else
      Error("statement expected");
    end if;

    Check_Separator;
  end Statement;
end State;
