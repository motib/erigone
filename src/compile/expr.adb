-- Copyright 2009-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Ada.Strings.Fixed;
with Compiler_Declarations, Compiler_Global, Lexer, Util;
use  Compiler_Declarations, Compiler_Global, Lexer, Util;
package body Expr is
  -- Compile the array selector. A is the table index of the array
  procedure Selector(A: in Integer) is
  begin
    if Tab(A).Typ /= Arrays then Error ("array expected"); end if;
    In_Symbol;
    Expression;
    Emit (Check_Index, Tab(A).Len, 0);
    Check_Symbol(rbracket_sy, "]");
  end Selector;

  -- Remote reference: Id contains "proctype@label"
  -- Emit remote_ref with process number and state number of label
  -- Loc cannot be used because we are interested in the "label"
  --   that occurs within "proctype"; when the label was encountered,
  --   this was stored in the "len" field of its symbol
  procedure Remote_Reference is
    use Ada.Strings.Fixed;
    S:       String  := Trim(Id);
    At_Sign: Natural := Index(S, "@");
    -- Index of "proctype" in the symbol table
    I:       Integer := Loc(Pad(S(1 .. At_Sign-1)));
    Label:   String  := S(At_Sign+1 .. S'Length);
    J:       Integer := T;
    Number:  Integer := Tab(I).Adr;  -- Process number
  begin
    Tab(0).Name := Pad(Label);   -- Sentinel
    Tab(0).Len  := Number;
    -- Search label for same process number
    while (Tab(J).Name /= Pad(Label)) or else (Tab(J).Len /= Number) loop
      J := J - 1;
    end loop;
    if J = 0 then Error("label not found"); end if;
    Emit(remote_ref, Tab(J).Len, Tab(J).Adr);
    In_Symbol;
  end Remote_Reference;

  -- Compile an expression using recursive subprogram for factors, etc.
  procedure Expression is
    Op : Symbol;

    procedure Relationalexpression is
      Op: Symbol;
    
      procedure Simpleexpression is
        Op : Symbol;
  
        procedure Term is
          Op : Symbol;
  
          procedure Factor is
            I, Lv: Integer;
            Op : Symbol;
          begin
            -- LHS of expression already compiled, so return
            if LHS_Array then
              LHS_Array := False;
              return;
            end if;
            while Factor_Begin_Sy(Sy) loop
              -- Identifier
              if Sy = Ident_Sy then
                -- Anonymous variable is OK for receive statement
                if Emit_Load_Address and then Id = Pad("_") then
                  Emit(anon_address, 0, 0);
                  In_Symbol;
                  return;
                end if;
                I := Loc(Id);
                if I = 0 then Error("identifier " & Trim(Id) & " not declared"); end if;
                In_Symbol;
                -- Variable or Parameter
                if Tab(I).Lev > 0 then Lv := 1; else Lv := 0; end if;
                if Tab(I).Obj = Variable or Tab(I).Obj = Parameter then
                  if Sy = Lbracket_Sy then  -- Array
                    Selector(I);
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
                    -- For receive statements, load address not value
                    if Emit_Load_Address then
                      Emit(load_address, Tab(I).Adr, Lv);
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
                  end if;

                -- For Mtype identifier, load its code
                elsif Tab(I).Obj = Mtype then
                  Emit(byte_push, Tab(I).Adr, 0);
                else
                  Error ("identifier " & Trim(Id) & " not declared");
                end if;

              -- Integer constant
              elsif Sy = intcon_sy then
                for N in 0 .. Number_Counter loop
                  if Inum = I_Tab (N) then
                    Emit (Load_const, N, 0);
                    exit;
                  end if;
                end loop;
                In_Symbol;
  
              -- True or false
              elsif Sy = True_Sy then
                Emit (byte_push, 1, 0);
                In_Symbol;
              elsif Sy = False_Sy then
                Emit (byte_push, 0, 0);
                In_Symbol;

              -- Parenthesized expression
              elsif Sy = Lparent_Sy then
                In_Symbol;
                Expression;
                if Sy = arrow_sy then  -- conditional expression
                  Emit(cond_expr, 0, 0);
                  In_Symbol;
                  Expression;
                  Check_Symbol(colon_sy, ":");
                  Emit(cond_expr, 1, 0);
                  Expression;
                  Emit(cond_expr, 2, 0);
                end if;
                Check_Symbol(rparent_sy, ")");
  
              -- Unary negation
              elsif Sy = Exclamation_Sy then
                In_Symbol;
                Factor;
                Emit (Logic_Not, 0, 0);
  
              -- Predefined functions and channel functions
              elsif Sy = pid_fun_sy then
                Emit(pid, 0, 0);
                In_Symbol;
              elsif Sy = nr_pr_sy then
                Emit(nrpr, 0, 0);
                In_Symbol;
              elsif sy = len_sy  or sy = empty_sy or sy = nempty_sy or
                    sy = full_sy or sy = nfull_sy then
                Op := Sy;
                In_Symbol;
                Check_Symbol(lparent_sy, "(");
                Expression;
                case Op is
                  when len_sy    => Emit(channel_len,    0, 0);
                  when empty_sy  => Emit(channel_empty,  0, 0);
                  when nempty_sy => Emit(channel_nempty, 0, 0);
                  when full_sy   => Emit(channel_full,   0, 0);
                  when nfull_sy  => Emit(channel_nfull,  0, 0);
                  when others    => null;
                end case;
                Check_Symbol(rparent_sy, ")");
              elsif sy = remote_sy then
                Remote_Reference;
              end if;
            end loop;
          end Factor;
  
        begin -- term 
          Factor;
          while Sy = Times_Sy or Sy = Idiv_Sy or Sy = Imod_Sy loop
            Op := Sy;   -- Save symbol before compiling right operand
            In_Symbol;
            Factor;
            case Op is
              when Times_Sy => Emit (Imul, 0, 0);
              when Idiv_Sy  => Emit (Idiv, 0, 0);
              when IMod_sy  => Emit (Irem, 0, 0);
              when others   => null;
            end case;
          end loop;
        end Term;
  
      begin -- simpleexpression
        -- Unary + or -
        if (Sy = Plus_Sy) or (Sy = Minus_Sy) then
          Op := Sy;    -- Save symbol before compiling operand
          In_Symbol;
          Term;
          if Op = Minus_Sy then Emit (Ineg, 0, 0); end if;
        else
          Term;
        end if;

        -- Binary adding operators
        while (Sy = plus_sy)     or (Sy = minus_sy)   or
              (Sy = right_sh_sy) or (Sy = left_sh_sy) loop
          Op := Sy;
          In_Symbol;
          Term;
          case Op is
            when plus_sy     => Emit (iadd,        0, 0);
            when minus_sy    => Emit (isub,        0, 0);
            when left_sh_sy  => Emit (left_shift,  0, 0);
            when right_sh_sy => Emit (right_shift, 0, 0);
            when others      => null;
          end case;
        end loop;
      end Simpleexpression;

      begin -- relationalexpression
        Simpleexpression;
        case Sy is
          when Eql_Sy | Neq_Sy | Gtr_Sy | Lss_Sy | Leq_Sy | Geq_Sy |
               bitand_sy | bitor_sy | xor_sy =>
            if Is_Copy then return; end if; -- ch ! <...>
            Op := Sy;    -- Save symbol before compiling right operand
            In_Symbol;
            Simpleexpression;
            case Op is
              when Eql_Sy    => Emit (Icmpeq, 0, 0);
              when Neq_Sy    => Emit (Icmpne, 0, 0);
              when Lss_Sy    => Emit (Icmplt, 0, 0);
              when Leq_Sy    => Emit (Icmple, 0, 0);
              when Gtr_Sy    => Emit (Icmpgt, 0, 0);
              when Geq_Sy    => Emit (Icmpge, 0, 0);
              when bitand_sy => Emit (bitand, 0, 0);
              when bitor_sy  => Emit (bitor,  0, 0);
              when xor_sy    => Emit (bitxor, 0, 0);
              when others    => null;
            end case;
          when others => null;
        end case;
      end Relationalexpression;

  begin -- expression
    Relationalexpression;
    -- Binary logical operators
    while Sy = Or_Sy or Sy = And_Sy loop
      Op := Sy;     -- Save symbol before compiling right operand
      In_Symbol;
      if Op = Or_Sy then Emit(Logic_Or, 1, 0);
      else               Emit(Logic_And, 1, 0);
      end if;
      Relationalexpression;
      if Op = Or_Sy then Emit(Logic_Or, 0, 0);
      else               Emit(Logic_And, 0, 0);
      end if;
    end loop;
  end Expression;
end Expr;
