-- Copyright 2008-9 by Mordechai (Moti) Ben-Ari. See version.ads
--
-- Verify acceptance, optionally with fairness
--
with Automata, Global, Hash_Tables, Location_Stack;
with Options, State_Stack, State_Vectors, Utilities;
package body Execute.Verify.Acceptance is
  use type Global.Byte, State_Vectors.State_Vector, Options.Execution_Type;

  procedure Search is
    -- The Seed is a copy of an accepting state that is searched
    --   for in the inner search; see p. 179 of SMC
    Seed:      State_Vectors.State_Vector := State_Vectors.Zero_Vector;
    Inner:     Global.Byte := 0;             -- Flag for inner search
    Location:  Location_Stack.Location_Item; -- Current location
    Inserted:  Boolean;  -- Was insert in hash table successful?
  begin
    -- Precondition: initial state and its locations are pushed onto
    --   their stacks; the initial state is in the hash table

    -- Compute the number of "unfolded" processes for fairness
    --   It does not include the never claim
    --   It does not include non-active proctypes
    --   These are computed when "run" is executed
    -- The bias is used when there are non-active proctypes that
    --   must be ignored
    --   Assume that these come at the beginning of the program 
    Unfolded_Bias := 0;
    for P in 0 .. Automata.Processes-1 loop
      if Automata.Program(P).PID = Global.None then
        Unfolded_Bias := Unfolded_Bias + 1;
      else
        exit;
      end if;
    end loop;

    Unfolded := 1;
    for P in 0 .. Automata.Processes-1 loop
      if Automata.Program(P).PID /= Global.None then
        Unfolded := Unfolded + 1;
      end if;
    end loop;
    if Options.Display(Options.Program) then
      Utilities.put("unfolded=", Unfolded);
      Utilities.put("unfolded bias=", Unfolded_Bias, True);
    end if;

    loop
      Increment_Steps;
      -- Get the top transition and the top state
      --   Set the Inner flag from the flag in the state
      Current := State_Stack.Top;
      Inner := Current.Inner;
      Atomic := Current.Atomic;
      Location := Location_Stack.Top;

      -- If top transition has been visited, pop it
      if Location.Visited then
        Location_Stack.Pop;

        if Location.Last then  -- last location from a state
          -- Accepting state, set the seed and start the inner search
          -- With fairness, set the seed on all states in the last copy
          if Inner = 0 and
             (  (Options.Execution_Mode = Options.Acceptance and
                   Is_Accept_State(Current)) or
                (Options.Execution_Mode = Options.Fairness and
                   Current.Fair = Unfolded)) then
            Inner := 1;
            Current.Inner := Inner;
            Seed := Current;

            if Options.Display(Options.Hash) then
              State_Vectors.Put_State_Vector("seed=,", Seed);
            end if;

            -- Push the Current state and get and push the transitions
            State_Stack.Push(Current);
            Get_And_Push_Transitions;

          else  -- Last location from a state, but 
                --   not and inner search and
                --   not an accepting state or the last fairness copy
            State_Stack.Pop(State_Stack.No_More_Transitions);
            exit when State_Stack.Empty;
            Current := State_Stack.Top;

            -- If a state of the outer search was popped,
            --   reset the Inner flag and Seed
            if Inner = 1 and Current.Inner = 0 then
              State_Stack.Pop(State_Stack.End_Of_Inner_Search);
              Inner := 0;
              Seed := State_Vectors.Zero_Vector;
            end if;
          end if;  -- accept state
        end if;  -- last location from state

      else  -- the location was not visited
        -- Set visited and execute the statement on the transition
        Location_Stack.Set_Visited;
        Execute_At(Location.L);

        -- If there is never claim, change the state of the never process
        if Automata.Never /= Global.None then
          Execute_Never(Location.Never); 
        end if;

        -- For fairness, go to the correct unfolded copy
        if Options.Execution_Mode = Options.Fairness then
          -- If accept state in 0th copy, go to 1st copy
          if Current.Fair = 0 and Is_Accept_State(Current) then
            Current.Fair := 1;
          -- If in i'th copy, go to i+1'st copy
          elsif Current.Fair = Location.L.Process + 1 then
            Current.Fair := Current.Fair + 1;
          -- If in last copy, go to 0th copy
          elsif Current.Fair = Unfolded then
            Current.Fair := 0;
          end if;
        end if;

        -- During the inner search, if a state is found
        ---  that is the same as the seed,
        --   an acceptance cycle has been found
        if Inner = 1 and Current = Seed then
          if Options.Display(Options.Hash) then
            State_Vectors.Put_State_Vector(
              "current state matches seed=,", Current);
          end if;
          raise Global.Counterexample_Error with "acceptance cycle";

        -- Or, the new state can be found on the stack
        elsif Inner = 1 and State_Stack.On_Stack(Current) /= -1 then
          -- Save index of stack element that starts the cycle
          Start_Of_Acceptance_Cycle := State_Stack.On_Stack(Current);
          if Options.Display(Options.Hash) then
            State_Vectors.Put_State_Vector(
              "current state matches stack element=" &
              Utilities.Trim(Integer'Image(Start_Of_Acceptance_Cycle)) & ",",
              State_Stack.Get_Element(Start_Of_Acceptance_Cycle));
          end if;
          raise Global.Counterexample_Error with "acceptance cycle";
        end if;

        -- Insert the new state in the hash table, if possible
        Hash_Tables.Put_State(Current, Inserted);

        if Inserted then
          -- If inserted, push the state and
          --   get and push the transitions from this state
          State_Stack.Push(Current);
          Get_And_Push_Transitions;
        end if;
      end if;  -- location visited
    end loop;
  exception
    when others =>
      Exception_Transition :=
        Automata.Program(Location.L.Process).
          Transition_List(Location.L.Transition);
      raise;
  end Search;
end Execute.Verify.Acceptance;
