-- Copyright 2008-11 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Interface to the compiler
--  The only package with'ed by both the compiler and the model checker
--
package Compiler_Declarations is
  -- -- Exceptions exported by the compiler
  File_Error:        exception;
  Compilation_Error: exception;

  -- The instructions for the virtual machine
  type Opcode is (
    -- Noop (default)
    noop,

    -- Built-in operations
    assert, halt, pid, nrpr, run, printf, remote_ref,

    -- Promela else for guarded commands
    logic_else,

    -- Computation on the stack
    iadd, idiv, imul, ineg, irem, isub,
    icmpeq, icmpne, icmplt, icmple, icmpgt, icmpge, cond_expr,
    logic_and, logic_not, logic_or,
    bitand, bitnot, bitor, bitxor,
    left_shift, right_shift,

    -- Stack manipulation
    --   Op1 is the offset
    --   Op2 is 0 for global, 1 for local
    byte_push,       -- Push an immediate byte operand (Op1)
    load_const,      -- Push a constant from the number table (Op1)
    byte_load, short_load, int_load,
                  -- Push from memory
    load_address, -- Push address of variable for receive
    anon_address, -- Load anonymous address for receive
    byte_store, short_store, int_store,
                  -- Pop top of stack to memory
    anon_store,   -- Store to an anonymous variable

    -- Arrays
    byte_aload, short_aload, int_aload,
                  -- Load value from an array
                  -- The index is on the top of stack
    byte_astore, short_astore, int_astore,
                  -- Store value into an array
                  -- The value is on the top of the stack,
                  -- The index is just below it on the stack
    check_index,  -- Check the index that the at the top of the stack  
                  --   is less than a value (Op1).

    -- Channel instructions
    fifo_send, sorted_send, move_fifo_receive, copy_fifo_receive,
    move_random_receive, copy_random_receive,
    fifo_poll, random_poll,
    
    -- Channel functions
    channel_len, channel_empty, channel_nempty,
    channel_full, channel_nfull
  );

  type Executable_Type is (Always, Expression, Channel);
  Executable: constant array(Opcode) of Executable_Type :=
    (
      noop | halt | pid | nrpr | run | printf | remote_ref => Always,
      assert | logic_else => Always,

      iadd | idiv | imul | ineg | irem | isub |
      icmpeq | icmpne | icmplt | icmple | icmpgt | icmpge | cond_expr |
      logic_and | logic_not | logic_or |
      bitand | bitnot | bitor | bitxor |
      left_shift | right_shift => Expression,

      byte_push | load_const | byte_load | short_load | int_load =>
        Expression,
      load_address | anon_address | byte_store | short_store |
      int_store | anon_store => Always, 
      byte_aload | short_aload | int_aload => Expression,
      byte_astore | short_astore | int_astore | check_index => Always,

      fifo_send | sorted_send | move_fifo_receive | copy_fifo_receive |
      move_random_receive | copy_random_receive |
      fifo_poll | random_poll |
      channel_len | channel_empty | channel_nempty |
      channel_full | channel_nfull => Channel
    );

  Data_Size: constant array(OpCode) of Natural := (
      byte_load  | byte_store  | byte_aload  | byte_astore  => 1,
      short_load | short_store | short_aload | short_astore => 2,
      int_load   | int_store   | int_aload   | int_astore   => 4,
      others => 0);
    
  -- Compile a source file and write the automata file
  procedure Compile_File(
    Source_File_Name: in String; Automata_File_Name: in String);
  
  -- Compile an expression (from an LTL formula)
  --   Return a string with the byte codes
  function Compile_Expression(Expression: String) return String;
  -- Get numbers after compiling LTL which might have a constant
  function Get_I_Tab return String;
end Compiler_Declarations;
