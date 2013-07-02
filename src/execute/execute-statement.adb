-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO, Ada.Strings.Fixed, Ada.Unchecked_Conversion;
with Interfaces.C;
with Automata.Display, Compiler_Declarations, Config;
with Options, Symbol_Tables, Utilities;
package body Execute.Statement is
  use Global, State_Vectors, Compiler_Declarations;
  use type Options.Execution_Type;

  -- Evaulate the byte Code (of length Size) in the Current state
  -- For a statement, it also updates the state vector
  --   so the parameter Current is of mode in-out
  -- The Result of an expression is returned to the caller
  --   (1 for a statement that does not evaluate an expression)
  -- Process_ID is used for computing "_pid" and
  --   as the index for the frame of local variables
  -- Extra is the channel index for and array of channels
  procedure Evaluate(
      Current:    in out State_Vectors.State_Vector; 
      Size:       Byte;
      Code:       access Automata.Byte_Code_Array;
      Process_ID: Byte;
      Extra:      Byte;
      Result:     out Integer) is

    -- A small local stack is used for interpretation of the byte code
    Stack: array(Config.Interpret_Index) of Integer;
    Top:   Config.Interpret_Index;

    -- Set the frame index for the local variables
    Frame_Index: Byte := Automata.Program(Process_ID).PID + 1;

    -- For receive, which arguments are variables and which are values
    --   Is_Variable = 0 when load is used
    --   Is_Variable = 1 when load_address is used
    --   Is_Variable = 2 when an anonymous variable is used
    Is_Variable:    Byte_Array_Base(Config.Message_Index);
    Arg_Count:      Byte;

    -- The byte code currently being interpreted
    B:               Automata.Byte_Code;
    -- The instruction pointer within the byte code array 
    IP:              Byte;
    -- Temporary integer and byte variables
    Reg, Reg1, Reg2: Integer;            -- For computation
    Op, Op1, Op2:    Byte;               -- Operands as bytes

    -- Stack instructions
    procedure Push(N: Integer) is
    begin
      Stack(Top) := N;
      Top := Top + 1;
    end Push;
    pragma Inline(Push);

    -- Push a byte by converting to an integer    
    procedure Push_Byte(N: Byte) is
    begin
      Stack(Top) := Integer(N);
      Top := Top + 1;
    end Push_Byte;
    pragma Inline(Push_Byte);
    
    function Pop return Integer is
    begin
      Top := Top - 1;
      return Stack(Top);
    end Pop;
    pragma Inline(Pop);
    
    function Get_Top return Integer is
    begin
      return Stack(Top-1);
    end Get_Top;
    pragma Inline(Get_Top);


    -- Print data for debugging the interpreter
    procedure Print_Debug is
    begin
      Ada.Text_IO.Put("frame=");
      Utilities.Put(Frame_Index);
      Ada.Text_IO.Put("code=" & 
        Utilities.To_Lower(Opcode'Image(B.Operator)) & 
        Byte'Image(B.Operand1) & Byte'Image(B.Operand2) & ",");
      Ada.Text_IO.Put("stack=");
      if Top = 1 then Ada.Text_IO.Put(","); end if;
      for I in 1..Top-1 loop
        Utilities.Put(Stack(I));
      end loop;
      Ada.Text_IO.New_Line;
    end Print_Debug;


    -- Interpret printf("format specifier string", arguments ...)
    -- The first operand is the index into the string table
    --   for the format specifier string
    -- The second operand is the count of the arguments
    --   which have been pushed onto the stack
    procedure Interpret_Printf is
      use Ada.Text_IO, Ada.Strings.Fixed;
      -- Get the format specifier string
      S:         String := Symbol_Tables.Get_String(B.Operand1);
      Specifier: Natural;              -- Index of a specifier in S
      Start:     Positive := S'First;  -- Index into S
    begin
      for I in 1 .. B.Operand2 loop   -- For each argument
        Specifier := Index(S(Start..S'Last), "%");
        if Specifier = 0 then
          raise Unexpected_Input with "not enough format specifiers";
        end if;

        -- Put the string up to the specifier
        Put(S(Start..Specifier-1));

        -- Put the data according to the specifier
        if S(Specifier+1) = 'd' then
          Put(Trim(Integer'Image(Pop), Side => Ada.Strings.Both));
        elsif S(Specifier+1) = 'c' then
          Put(Character'Val(Pop));
        elsif S(Specifier+1) = 'e' then
          Put(Symbol_Tables.Get_MType(Byte'Mod(Pop)));
        else
          raise Unexpected_Input with "unrecognized format specifier";
        end if;
        Start := Specifier + 2;
      end loop;

      -- Print the remainder of the specifier string,
      --   and put a new line if there is \n at the end
      if S(S'Last-1..S'Last) = "\n" then
        Put_Line(S(Start..S'Last-2));
      else
        Put(S(Start..S'Last));
      end if;
    end Interpret_Printf;


    -- Interpret the channel instructions
    procedure Channel_Instructions is
      use Symbol_Tables;

      -- The index of the channel for the instruction is on top of stack
      Channel_Index:       Byte := Byte'Mod(Pop);
      Channel:             Symbol_Tables.Channel renames
        Get_Channel(Channel_Index);

      -- Declare local variables for the channel data
      -- The size of the channel buffer
      Buffer_Size:         Byte := Channel.Buffer_Size;
      -- The offset of the channel buffer in the state vector
      Offset_Of_Channel:   Byte := Channel.Offset;
      -- The number of fields in a message
      Fields_In_Message:   Byte := Channel.Elements;
      -- The total size of a single message
      Message_Size:        Byte := Channel.Message_Length;

      -- The number of messages currently in the channel buffer
      --   is in the first byte for the channel in the state vector
      Elements_In_Channel: Byte :=
        Get_Byte_Variable_Value(Current, Offset_Of_Channel);

      -- Variables used when iterating over elements in a message:
      Element_Size:        Byte;  -- The size of a single element
      Addr:                Byte;  -- Address counter

      -- Pop values to send and save them here
      --   For sorted send, the values are used for matching messages
      Message_Buffer:      array(Config.Message_Index) of Integer;
      M:                   Integer;

      -- For receive:
      --   Messages to search in channel (1 for FIFO)
      Messages_To_Search:  Byte;
      --   Index where random message is found
      Random_Index:        Byte;
      --   Success flag during random search
      Success:             Boolean;

      -- Start of message is offset of channel + 1 for the number of
      --   messages + M times the number of messages
      function Start_Of_Message(M: Byte) return Byte is
      begin
        return Offset_Of_Channel + 1 + M * Message_Size;
      end Start_Of_Message;
      pragma Inline(Start_Of_Message);
        
    begin
      case B.Operator is

        --------------- Channel expressions -------------
        when channel_len    => Push_Byte(Elements_In_Channel);

        when channel_empty  =>
          Push(Boolean'Pos(Elements_In_Channel = 0));

        when channel_nempty => 
          Push(Boolean'Pos(Elements_In_Channel /= 0));

        when channel_full   =>
          Push(Boolean'Pos(Elements_In_Channel = Buffer_Size));

        when channel_nfull  =>
          Push(Boolean'Pos(Elements_In_Channel /= Buffer_Size));


        ------------- FIFO Send -------------
        when fifo_send =>
          -- Set Handshake for rendezvous channel
          if Buffer_Size = 0 then
            Handshake := Channel_Index;
          end if;

          -- Move all elements from the stack to the channel
          Addr := Start_Of_Message(Elements_In_Channel);
          for I in 0..B.Operand1-1 loop
            Element_Size := Channel.Element_Sizes(I); 
            Update_Variable_By_Size(Current, Addr, Element_Size, Pop);
            Addr := Addr + Element_Size;
          end loop;

          -- Increment the number of elements in the channel
          Update_Byte_Variable(
            Current, Offset_Of_Channel, Elements_In_Channel+1);
          Push(1);

        ------------- Sorted Send -------------
        when sorted_send =>
          -- Get all elements of the message from the stack
          for I in 0 .. Fields_In_Message-1 loop
            Message_Buffer(I) := Pop;
          end loop;
  
          -- Set a sentinel after the last message in the channel,
          --   so that the search will always succeed
          Element_Size := Channel.Element_Sizes(0);
          Addr := Offset_Of_Channel+1 + 
                  Elements_In_Channel * Message_Size;
          Update_Variable_By_Size(
            Current, Addr, Element_Size, Integer'Last);
  
          -- Find the first message that is greater then the new one
          Inserted:
          for I in 0 .. Elements_In_Channel loop
            Addr := Start_Of_Message(I); 
            for J in 0 .. Fields_In_Message-1 loop
              Element_Size := Channel.Element_Sizes(J);
              M := Get_Variable_Value_By_Size(
                     Current, Addr, Element_Size);
              if Message_Buffer(J) > M then    -- New element is larger
                exit;
              elsif Message_Buffer(J) = M then -- Try next element
                Addr := Addr + Element_Size;
              else                             -- New element is smaller
                -- Move the rest of the messages to make room
                for K in reverse I+1 .. Elements_In_Channel loop
                  Update_Variable(
                    Current, Offset_Of_Channel+1 + K * Message_Size,
                    Get_Variable_Value(
                      Current,
                      Offset_Of_Channel+1 + (K-1) * Message_Size,
                      Message_Size)); 
                end loop;
                -- Move the new message into place
                Addr := Start_Of_Message(I); 
                for K in 0..B.Operand1-1 loop
                  Element_Size := Channel.Element_Sizes(K);
                  Update_Variable_By_Size(
                    Current, Addr, Element_Size, Message_Buffer(K));
                  Addr := Addr + Element_Size;
                end loop;
                exit Inserted;
              end if;
            end loop;
          end loop Inserted;
  
          -- Increment the number of elements in the channel
          Update_Byte_Variable(
            Current, Offset_Of_Channel, Elements_In_Channel+1);
          Push(1);

        ------------- Receive -------------
        when move_fifo_receive   | copy_fifo_receive   |
             move_random_receive | copy_random_receive |
             fifo_poll           | random_poll =>
          -- Set Handshake for rendezvous channel
          if Buffer_Size = 0 then
            Handshake := 0;
          end if;

          if B.Operator = move_fifo_receive or
             B.Operator = copy_fifo_receive or
             B.Operator = fifo_poll         then
            -- FIFO: check only the first element in the channel
            Messages_To_Search := 1;
            Random_Index       := 1;
          else
            -- Random: check all elements in the channel
            Messages_To_Search := Elements_In_Channel;
          end if;

          -- For random receive, we will need the arguments
          --   more than once, so pop and save them
          for F in 0..B.Operand1-1 loop
            Message_Buffer(F) := Pop;
          end loop;
  
          Channel_Messages_Loop:
          for E in 0..Messages_To_Search-1 loop
            Addr := Start_Of_Message(E);
            Success := True;
  
            Message_Elements_Loop:
            for I in 0 .. B.Operand1-1 loop
              Element_Size := Channel.Element_Sizes(I); 

              -- If the argument is a variable:
              --   Copy elements from the channel
              --     to variables in the state vector,
              --     but not if poll instructions (side-effect free)
              --   The offsets of the variables were popped
              --     to the Message_Buffer
              --   Add 1 to offset to skip count of elements in channel
              if Is_Variable(B.Operand1-1-I) = 1 then
                if B.Operator /= fifo_poll and
                   B.Operator /= random_poll then
                  Update_Variable_By_Size(
                    Current, Byte'Mod(Message_Buffer(I)), Element_Size,
                    Get_Variable_Value_By_Size(
                      Current, Addr, Element_Size ));
                end if;

              -- If the argument is an anonymous variable
              elsif Is_Variable(B.Operand1-1-I) = 2 then
                null;
  
              -- If the argument is a value (constant or eval)
              --   Check if the value on the stack equals the value
              --     in the channel; if not, set Result = 0
              else
                if Message_Buffer(I) /=
                     Get_Variable_Value_By_Size(
                       Current, Addr, Element_Size) then
                  Success := False;
                  exit Message_Elements_Loop;
                end if;
              end if;
              Addr := Addr + Element_Size;
            end loop Message_Elements_Loop;
  
            Random_Index := E;  -- Loop index for use outside loop
            exit Channel_Messages_Loop when Success;
          end loop Channel_Messages_Loop;

          -- If move - not copy or poll - update channel in state vector
          --   Close up channel elements
          --     Move Random_Index   .. Elements_In_Channel elements
          --     to elements at Random_Index-1 .. Elements_In_Channel-1
          if Success and
               (B.Operator = move_fifo_receive or
                B.Operator = move_random_receive) then
            if Elements_In_Channel > 1 then
              for I in Random_Index .. Elements_In_Channel-1 loop
                Addr := Start_Of_Message(I);
                Update_Variable(
                  Current, Addr,
                  Get_Variable_Value(
                    Current, Addr + Message_Size, Message_Size));
              end loop;
            end if;

            -- Put zeros in place of deleted message for comparing
            --   equivalent state vectors in hash table
            Addr := Start_Of_Message(Elements_In_Channel-1);
            Update_Variable(Current, Addr, (0..Message_Size-1 => 0));

            -- Decrement the number of elements in the channel
            Update_Byte_Variable(
              Current, Offset_Of_Channel, Elements_In_Channel-1);
          end if;  -- Move - not copy
          Push(Boolean'Pos(Success));

        when others => null;
      end case;
    end Channel_Instructions;


    -- Interpret "run"
    --   The arguments are evaluated in reverse order,
    --   then the "run" instruction and then "store" instructions
    -- Operand1 contains the proctype index+1
    procedure Run_Instruction is
      New_Process: Byte;  -- Index of new processes
    begin
      -- If there is a never claim, it will be at the never claim's
      --   index and the never claim will be moved
      if Automata.Never /= None then
        New_Process := Automata.Processes-1;
      end if;

      -- Make 1 copy of the proctype B.Operand1
      Automata.Replicate_Proctype(
        B.Operand1-1, Automata.Program(B.Operand1-1).Copies + 1);

      -- If there is no never claim, the new process is the last one
      if Automata.Never = None then
        New_Process := Automata.Processes-1;
      end if;

      -- Set the initial transition in the Current state vector
      State_Vectors.Update_Process_Location(
        Current, New_Process,
        Automata.Get_Process_Initials(New_Process));
      Frame_Index := Automata.Program(New_Process).PID + 1;

      -- For copies of processes in fairness
      Unfolded := Unfolded + 1;

      -- Display the new process
      if Options.Display(Options.Program) then
        Ada.Text_IO.Put_Line("new copy of process=" &
          Utilities.Trim(Automata.Program(B.Operand1-1).Identifier) &
          ",");
        Automata.Display.Put_One_Process(New_Process);
        Utilities.put("unfolded=", Unfolded, True);
        Ada.Text_IO.Put_Line("new copy end=,");
        Symbol_Tables.Put_Frame_Table;
      end if;
    end Run_Instruction;

  begin -- Evaluate
    -- Initialization for receive statements
    Arg_Count   := 0;
    Is_Variable := (others => 0);

    -- Zero element is not used so that Top can be decremented
    Top := 1; Stack(0) := 0;

    IP := 0;
    while IP < Size loop
      B := Code.all(IP);
      if Options.Debug(Options.Debug_Interpreter) then
        Print_Debug;
      end if;

      case B.Operator is
        when noop   => null;

        when assert => null;

        when halt   => raise Termination_Error with "halt executed";

        when printf => -- Print only during simulation
          if Options.Execution_Mode = Options.Simulation then
            Interpret_Printf;
          end if;

        when pid    =>
          Push_Byte(Automata.Program(Process_ID).PID);
          Arg_Count := Arg_Count + 1;
        
        when nrpr   => Push_Byte(Execute.Compute_NRPR);

        when run    => 
          -- Don't execute run again when backtracking
          if B.Operand2 = 0 then
            Run_Instruction;       
            Code.all(IP).Operand2 := 1;
          end if;

        -- Remote reference
        --   Operand1-1 = process number, Operand2 = state number
        when remote_ref =>
          Push(Boolean'Pos(
            Get_Process_Location_Value(Current, B.Operand1-1) =
            B.Operand2));

        -- Load constant and immediate operands
        --   For receive statement, skip setting Is_Variable
        when load_const =>
          Push(Symbol_Tables.Get_Number(B.Operand1));
          Arg_Count := Arg_Count + 1;

        when byte_push =>
          Push_Byte(B.Operand1);
          Arg_Count := Arg_Count + 1;

        -- Load address used for variables in receive statements
        --   Set the Is_Variable flag for this argument
        when load_address =>
          Op1 := B.Operand1;
          if B.Operand2 /= 0 then
            Op1 := Op1 + Symbol_Tables.Frame_Starts(Frame_Index);
          end if;
          Push_Byte(Op1);
          Is_Variable(Arg_Count) := 1;
          Arg_Count := Arg_Count + 1;

        -- Anonymous address and store
        when anon_address =>
          Push_Byte(B.Operand1);
          Is_Variable(Arg_Count) := 2;
          Arg_Count := Arg_Count + 1;
        when anon_store =>
          Reg := Pop;
          Push(1);

        -- Push a value onto the top of the stack
        --   For an array, the stack contains the index and element size
        when byte_load  | short_load  | int_load |
             byte_aload | short_aload | int_aload =>

          -- The offset of the variable
          Op1 := B.Operand1;
          -- Add frame offset for local variables
          if B.Operand2 /= 0 then
            Op1 := Op1 + Symbol_Tables.Frame_Starts(Frame_Index);
          end if;

          -- Multiply index by element size for arrays
          Op := Byte'Mod(Data_Size(B.Operator));
          if B.Operator = byte_aload or B.Operator = short_aload or
             B.Operator = int_aload then
            Op1 := Op1 + Byte'Mod(Pop) * Op;
          end if;

          Reg := Get_Variable_Value_By_Size(Current, Op1, Op);
          Push(Reg);
          Arg_Count := Arg_Count + 1;

        -- Store a value that is on the top of the stack
        -- For an array, the order is:
        --   ..., index, value, element size
        when byte_store  | short_store  | int_store |
             byte_astore | short_astore | int_astore =>

          -- The offset of the variable
          Op1 := B.Operand1;
          -- Add frame offset for local variables
          if B.Operand2 /= 0 then
            Op1 := Op1 + Symbol_Tables.Frame_Starts(Frame_Index);
          end if;

          -- Multiply index by element size for arrays
          Op := Byte'Mod(Data_Size(B.Operator));
          Reg := Pop;
          if B.Operator = byte_astore or B.Operator = short_astore or
             B.Operator = int_astore then
            Op1 := Op1 + Byte'Mod(Pop) * Op;
          end if;

          Update_Variable_By_Size(Current, Op1, Op, Reg);

        -- Check array bound:
        --   the index is on the top of the stack (but don't pop!)
        --   the bound is operand 1
        when check_index =>
          if B.Operand1 <= Byte'Mod(Get_Top) then
            raise Termination_Error with 
              "bounds error: index=" &
              Utilities.Trim(Integer'Image(Get_Top)) &
              " > length-1=" & Utilities.Trim(Byte'Image(B.Operand1-1));
          end if;


        -- Logical operators
        when logic_not =>
          if Pop = 0 then Push(1); else Push(0); end if;

        when logic_else => Push(1);

        -- B.Operand1 = 0 at the end of condition
        -- B.Operand1 = 1 at the end of the first expression
        -- B.Operand1 = 2 at the end of the second expression
        when cond_expr =>
          -- If the condition is false, skip to the second expression
          if B.Operand1 = 0 then
            Reg := Pop;
            if Reg = 0 then
              loop
                IP := IP + 1;
                exit when Code.all(IP).Operator = cond_expr;
              end loop;
            end if;

          -- At the end of first expression, skip to end of second
          elsif B.Operand1 = 1 then
              loop
                IP := IP + 1;
                exit when Code.all(IP).Operator = cond_expr;
              end loop;

          -- At the end of second expression, continue
          elsif B.Operand1 = 2 then
            null;
          end if;

        -- Short circuit operators:
        --   When short circuit occurs, skip over computation and
        --   just push what the result should be
        when logic_and =>
          if B.Operand1 = 0 then
            Reg2 := Pop;
            Reg1 := Pop;
            if Reg1 /= 0 and Reg2 /= 0 then Reg := 1; else Reg := 0; end if;
            Push(Reg);
          else -- B.Operand1 = 1
            Reg := Get_Top;
            if Reg = 0 then
              loop
                IP := IP + 1;
                exit when Code.all(IP).Operator = logic_and;
              end loop;
              Push(0);
            end if;
          end if;

        when logic_or =>
          if B.Operand1 = 0 then
            Reg2 := Pop;
            Reg1 := Pop;
            if Reg1 = 1 or Reg2 = 1 then Reg := 1; else Reg := 0; end if;
            Push(Reg);
          else -- B.Operand1 = 1
            Reg := Get_Top;
            if Reg = 1 then
              loop
                IP := IP + 1;
                exit when Code.all(IP).Operator = logic_or;
              end loop;
              Push(1);
            end if;
          end if;

        -- Arithmetic operators
        when ineg => Push(-Pop);

        when iadd   | isub  | imul   | idiv | irem =>
          Reg2 := Pop;
          Reg1 := Pop;
          case B.Operator is
            when iadd   => Reg := Reg1 + Reg2;
            when isub   => Reg := Reg1 - Reg2;
            when imul   => Reg := Reg1 * Reg2;
            when idiv   => Reg := Reg1 / Reg2;
            when irem   => Reg := Reg1 rem Reg2;
            when others => null;
          end case;
          Push(Reg);

        -- Bit operations only on the modular type Byte
        when bitand | bitor | bitxor | right_shift | left_shift =>
          Op2 := Byte'Mod(Pop);
          Op1 := Byte'Mod(Pop);
          case B.Operator is
            when bitand      => Op := Op1 and Op2;
            when bitor       => Op := Op1 or  Op2;
            when bitxor      => Op := Op1 xor Op2;
            when right_shift =>
              Op :=Byte(Interfaces.Shift_Right(
                     Interfaces.Unsigned_8(Op1), Natural(Op2)));
            when left_shift  =>
              Op := Byte(Interfaces.Shift_Left(
                     Interfaces.Unsigned_8(Op1), Natural(Op2)));
            when others => null;
          end case;
          Push(Integer(Op));

        -- Relational operators
        when icmpeq | icmpne | icmplt | icmple | icmpgt | icmpge =>
          Reg2 := Pop;
          Reg1 := Pop;
          Reg  := 0;
          case B.Operator is
            when icmpeq => if Reg1 =  Reg2 then Reg := 1; end if;
            when icmpne => if Reg1 /= Reg2 then Reg := 1; end if;
            when icmplt => if Reg1 <  Reg2 then Reg := 1; end if;
            when icmple => if Reg1 <= Reg2 then Reg := 1; end if;
            when icmpgt => if Reg1 >  Reg2 then Reg := 1; end if;
            when icmpge => if Reg1 >= Reg2 then Reg := 1; end if;
            when others => null;
          end case;
          Push(Reg);

        when fifo_send           | sorted_send         |
             move_fifo_receive   | copy_fifo_receive   |
             move_random_receive | copy_random_receive |
             fifo_poll           | random_poll         |
             channel_len         | channel_empty       |
             channel_nempty      | channel_full        |
             channel_nfull       =>

          -- For checking executability of a statement for a channel
          --   array, interpret the byte code up until the channel
          --   instruction; the top of the stack is the channel
          --   index and the rest of the operands can be popped
          if Extra /= 0 then
            Reg1 := Pop;
            for I in 0 .. B.Operand1-1 loop
              Reg2 := Pop;
            end loop;
            Push(Reg1);
            exit;
          else
            Channel_Instructions;
          end if;

        when others =>
          raise Internal_Error
            with "unrecognized byte code " & 
            Utilities.To_Lower(OpCode'Image(B.Operator));
      end case;

      IP := IP + 1;
    end loop;

    -- Return the top of the stack
    Result := Pop;
  end Evaluate;
end Execute.Statement;
