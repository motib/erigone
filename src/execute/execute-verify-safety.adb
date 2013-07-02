-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Global, Hash_Tables, Location_Stack, Options;
with State_Stack, Utilities;
package body Execute.Verify.Safety is
  procedure Search is
    Location:  Location_Stack.Location_Item; -- Current location
    Inserted:  Boolean;  -- Was insert in hash table successful?
    use type Global.Byte;
  begin
    -- Precondition: initial state and its locations are pushed onto
    --   their stacks; the initial state is in the hash table
    loop
      Increment_Steps;
      -- Get the top transition and the top state
      Current := State_Stack.Top;
      Atomic := Current.Atomic;
      Location := Location_Stack.Top;

      -- If the top transition has been visited, pop it
      if Location.Visited then
        Location_Stack.Pop;
        -- If this is the last transition for this state, pop the state
        if Location.Last then
          State_Stack.Pop(State_Stack.No_More_Transitions);
          exit when State_Stack.Empty;
        end if;
      else -- The top transition has not been visited,
        -- Mark it visited and execute it
        Location_Stack.Set_Visited;
        Execute_At(Location.L);

        -- If there is a never claim
        --   change the state of the never process
        if Automata.Never /= Global.None then
          Execute_Never(Location.Never);
        end if;

        -- Insert the new state into the hash table, if possible
        Hash_Tables.Put_State(Current, Inserted);

        --   If inserted, push the new state onto the stack,
        --   and get and push the transitions from the state
        if Inserted then
          State_Stack.Push(Current);
          Get_And_Push_Transitions;
        end if;
      end if;
    end loop;
  exception
    when others =>
      Exception_Transition :=
        Automata.Program(Location.L.Process).
          Transition_List(Location.L.Transition);
      raise;
  end Search;
end Execute.Verify.Safety;
