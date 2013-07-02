-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO;
with Automata.Display, Compiler_Declarations, Config, Global, LTL.Formulas;
with Options, Symbol_Tables, Utilities;
package body LTL.Automaton is
  -- Convert the tableau nodes to a Buchi automaton.
  -- N_Set is the set of nodes of the tableau
  -- LTL_Transitions is the array of transitions that is returned
  -- Count is the number of transitions in LTL_Transitions
  --
  -- Structure:
  --   Convert
  --     Get_Future_Formulas
  --       Find_Futures
  --         Find_In_Formulas
  --     Is_Accepting_State
  --     Create_Transition
  --       Get_Condition
  --       Incoming
  --     Put_Buchi
  --     Degeneralize
  --     Optimize
  --       Replace_State
  --         Remove_Duplicates
  --       Optimize_Loop
  --
  procedure Convert(
      N_Set:           in  Node_Sets.Set;
      LTL_Transitions: out Automata.Transition_Array;
      Count:           out Byte) is
    Future_Formulas: Formula_Sets.Set;

    -- Get the set of "future formulas" <>F that must be fulfilled
    -- Uses iterators over all nodes and all formulas in each OldF
    procedure Get_Future_Formulas is 
  
      -- Iterate this procedure for each node
      procedure Find_Futures(Position: in Node_Sets.Cursor) is
        N: Node := Node_Sets.Element(Position);
  
        -- Iterate this procedure for each formula in OldF
        procedure Find_In_Formulas(Position: in Formula_Sets.Cursor) is
          F: Formula_Ptr := Formula_Sets.Element(Position);
        begin
          if F.Token = Eventually or F.Token = Until_Op then
            Formula_Sets.Insert(Future_Formulas, F);
          end if;
        exception
          -- Ignore failure if formula is already in the set
          when Constraint_Error => null;
        end Find_In_Formulas;

      begin -- Find_Futures
        Formula_Sets.Iterate(N.OldF, Find_In_Formulas'Access);
      end Find_Futures;

    begin -- Get_Future_Formulas
      Node_Sets.Iterate(N_Set, Find_Futures'Access);

      if Options.Display(Options.LTL) then
        Ada.Text_IO.Put("formulas to be fulfilled=");
        LTL.Formulas.Put_Formula_Set(Future_Formulas);
        Ada.Text_IO.New_Line;
      end if;
    end Get_Future_Formulas;

    -- Return the accepting state flag for a transition with Source state
    -- Index is the number of the future formula within the set
    --   for use with generalized BAs
    function Is_Accepting_State(Source: Byte; Index: Byte)
        return Global.Byte is
      use Formula_Sets;
      Source_Node: Node;
      Position:    Cursor := First(Future_Formulas);
      F:           Formula_Ptr;
    begin
      -- Zero initial state has no formulas
      if Source = 0 then return 0; end if;

      -- If there are no future formulas, any state is accepting
      if Is_Empty(Future_Formulas) then return 1; end if;

      -- Get the formulas in the Source state and check if empty
      Source_Node := Node_Sets.Element(
        Node_Sets.Find(N_Set, (Source, others => <>)));
      -- If so, the state is accepting
      if Is_Empty(Source_Node.OldF) then return 1; end if;

      -- For generalized BAs, get the correct formula
      for I in 2 .. Index loop
        Next(Position);
      end loop;
      F := Element(Position);

      -- Accepting if a future formula _is not_ in the set of formulas
      --   of the Source state or if F _is_ in the set
      if not Contains(Source_Node.OldF, F) or else
             Contains(Source_Node.OldF, F.Right) then
        return 1;
      else
        return 0;
      end if;
    end Is_Accepting_State;

    -- Create a transition for this node and each element of Incoming
    procedure Create_Transition(Position: in Node_Sets.Cursor) is
      N: Node  := Node_Sets.Element(Position);

      -- Get the condition to be true for the transition
      --   This is the set of literals in N.OldF
      --   If there is more than one literal, create a conjunction
      function Get_Condition return Global.Name is
        use Formula_Sets;
        C:     Cursor;
        S, S1: Global.Name;
      begin
        if Formula_Sets.Is_Empty(N.OldF) then
          return Blanks;
        else
          C := First(N.OldF);
          S := LTL.Formulas.Get_Literal(Element(C));
          loop
            Next(C);
            exit when C = No_Element;
            -- Get next literal into S1 and add to S if not "1"
            S1 := LTL.Formulas.Get_Literal(Element(C));
            exit when S1 = Utilities.Pad("1") or 
                      S1 = Utilities.Pad("true"); 
            S := Utilities.Pad(Utilities.Trim(S) & "&&" & 
                 Utilities.Trim(S1));
          end loop;
          return S;
        end if;
      end Get_Condition;

      -- Iterate this procedure for each element of Incoming
      -- These elements are the source nodes of the transitions
      -- The Condition is the boolean expression that must be true
      --   for the transition to be taken
      procedure Incoming(Position: in Name_Sets.Cursor) is
        Source:    Byte := Name_Sets.Element(Position);
        End_Label: Byte := 0;
        Code_Size: Byte := 0;
        Byte_Code: Automata.Byte_Code_Array := (others => <>);
        Condition: Global.Name := Get_Condition;
        use type Options.Execution_Type;
      begin
        -- Set end label if no condition
        if Condition = Blanks then
          End_Label := 1;
        end if;

        -- Translate expression to byte code
        if Condition /= Blanks then
          Automata.Extract_Byte_Code(
            Compiler_Declarations.Compile_Expression(Condition),
            Code_Size, Byte_Code);
          loop
            declare
              I_Tab: String := Compiler_Declarations.Get_I_Tab;
            begin
              exit when I_Tab = "";
              Symbol_Tables.Set_Number(I_Tab);
            end;
          end loop;
        end if;

        -- Construct the transition
        --   Accept_Label is relevant only if one future formula
        LTL_Transitions(Count) :=
          (Source      => Source,
          Target       => N.N,
          Statement    =>
            new Line'(Utilities.Pad(Condition, Count => Line'Length)),
          End_Label    => End_Label,
          Accept_Label => Is_Accepting_State(Source, 1),
          Code_Size    => Code_Size,
          Byte_Code    => new Automata.Byte_Code_Array'(Byte_Code),
          others       => 0);
        Count := Count + 1;
      end Incoming;

    begin -- Create_Transition
      -- Iterate over each element of Incoming
      Name_Sets.Iterate(N.Incoming, Incoming'Access);
    end Create_Transition;

    -- Display the buchi automaton
    procedure Put_Buchi(Prefix: in String) is
    begin
      if Options.Display(Options.LTL) then
        Ada.Text_IO.Put_Line(Prefix & "buchi automaton start=,");
        for I in 0..Count-1 loop
          Automata.Display.Put_One_Transition(LTL_Transitions(I));
        end loop;
        Ada.Text_IO.Put_Line(Prefix & "buchi automaton end=,");
      end if;
    end Put_Buchi;

    -- Degeneralize the Buchi automata if the number of future
    --   formulas is greater than 1
    -- There are Copies of the states for each formula
    -- The state numbers in the copies are obtained
    --   by adding multiples of Offset, say 256/4 = 64
    procedure Degeneralize is
      Offset: constant := Byte'Modulus / Config.Max_Futures;
      Copies: Byte     := Byte(Formula_Sets.Length(Future_Formulas));
      -- Rename the variable for brevity
      T:  Automata.Transition_Array renames LTL_Transitions;
    begin
      if Count > Offset then
        raise Unexpected_Input
          with "too many transitions to degeneralize";
      end if;

      -- Create copies of the transitions
      for C in 1 .. Copies-1 loop
        -- Copy the transitions
        T(C*Count .. (C+1)*Count-1) := T(0..Count-1);
        -- For each state in the copy
        for I in C*Count .. (C+1)*Count-1 loop
          -- If the state is accepting, change the target to the next copy
          if Is_Accepting_State(T(I).Source, C+1) = 1 then
            T(I).Target := T(I).Target + Offset*((C+1) mod Copies);
          else  -- Not accepting, stay within the same copy
            T(I).Target := T(I).Target + Offset*C;
          end if;
          -- Change the source by adding the offset
          T(I).Source := T(I).Source + Offset*C;
          -- Clone the byte code
          T(I).Byte_Code := new Automata.Byte_Code_Array'(T(I).Byte_Code.all);
          -- Only the 0th copy is accepting, so change the flag
          T(I).Accept_Label := 0;
        end loop;
      end loop;

      -- Set accepting states in the 0th copy (0 through Count-1)
      --   and transitions from accepting states to 1st copy
      for I in 0..Count-1 loop
        T(I).Accept_Label := Is_Accepting_State(T(I).Source, 1);
        if T(I).Accept_Label = 1 then
          T(I).Target := T(I).Target + Offset;
        end if;
      end loop;

      Count := Count * Copies;
    end Degeneralize;

    -- Two states can be identified if the set of transitions coming
    --   out of them have the same target, statement and accept label
    procedure Optimize is
      Changed: Boolean;         -- A change has been made
      -- Rename the variable for brevity
      T:  Automata.Transition_Array renames LTL_Transitions;

      -- All occurrences of Replace changed to By
      procedure Replace_State(Replace, By: in Byte) is

        -- Remove duplicate transitions
        procedure Remove_Duplicates is
          Index1: Byte := 0;
          use type Automata.Transitions;
        begin
          if Count <= 1 then return; end if;
          while Index1 <= Count-2 loop
            for Index2 in Index1+1 .. Count-1 loop
              -- If two transitions are the same
              if T(Index1) = T(Index2) then
                T(Index2..Count-2) := T(Index2+1..Count-1);
                Count := Count - 1;
              end if;
            end loop;
            Index1 := Index1 + 1;
          end loop;
        end Remove_Duplicates;

      begin  -- Replace_State
        for I in 0 .. Count-1 loop
          if T(I).Source = Replace then
            T(I).Source := By;
          end if;
          if T(I).Target = Replace then
            T(I).Target := By;
          end if;
        end loop;
        Automata.Sort(T(0..Count-1));
        -- Put_Buchi("Replacing" & Byte'Image(Replace) & 
                  -- " by"       & Byte'Image(By) & " "); 

        Remove_Duplicates;
        Automata.Sort(T(0..Count-1));
        -- Put_Buchi("Removing duplicates "); 
      end Replace_State;

      procedure Optimize_Loop is
        N: Byte; -- Number of transitions with the same source state
      begin
        if Count <= 1 then return; end if;
        for Index1 in 0..Count-2 loop

          Second_Source_Loop:             -- Label for exit
          for Index2 in Index1+1 .. Count-1 loop
            -- Look for two transitions with different source
            --   states but otherwise the same
            if T(Index1).Source       /= T(Index2).Source and
               T(Index1).Target        = T(Index2).Target and
               T(Index1).Statement.all = T(Index2).Statement.all and
               T(Index1).Accept_Label  = T(Index2).Accept_Label then
             -- If there is another transition with the same source
              --   source state but otherwise different, do not replace
              --   Example: 5 -> 13, 13 -> 13 but 13 -> 14

              -- Check first that if there previous transitions
              --   with the same source states that didn't match
              if (Index1 > 0 and then 
                  T(Index1-1).Source = T(Index1).Source) or
                  T(Index2-1).Source = T(Index2).Source  then
                exit Second_Source_Loop;
              end if;

              N := 1;
              while Index2+N <= Count-1 loop
                -- When transitions are found with different sources,
                --   terminate the search because all transitions
                --   with with same source are OK
                -- Exit this loop and proceed to Replace_State
                exit when T(Index1+N).Source /= T(Index1).Source and
                          T(Index2+N).Source /= T(Index2).Source;
                -- Don't replace states if two transitions have
                -- the same sources but something else doesn't match
                exit Second_Source_Loop when
                  T(Index1+N).Target        /= T(Index2+N).Target or
                  T(Index1+N).Statement.all /= T(Index2+N).Statement.all or
                  T(Index1+N).Accept_Label  /= T(Index2+N).Accept_Label;
                N := N + 1;
              end loop;

              -- Replace source state of Index2 by that of Index1
              Replace_State(
                Replace => T(Index2).Source, By => T(Index1).Source);
              Changed := True;
              return;
            end if;
          end loop Second_Source_Loop;
        end loop;
      end Optimize_Loop;

    begin -- Optimize
      loop
        Changed := False;
        Optimize_Loop;
        exit when not Changed;
      end loop;
    end Optimize;

  begin -- Convert
    Count := 0;
    Get_Future_Formulas;
    Node_Sets.Iterate(N_Set, Create_Transition'Access);

    Automata.Sort(LTL_Transitions(0..Count-1));

    Put_Buchi("");
    if Byte(Formula_Sets.Length(Future_Formulas)) > 1 then
      Degeneralize;
      Put_Buchi("degeneralized ");
    end if;
    Optimize;
    Put_Buchi("optimized ");
  end Convert;
end LTL.Automaton;
