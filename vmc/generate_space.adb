-- Copyright 2011-12 by Mordechai (Moti) Ben-Ari. GNU GPL.
with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Global;      use Global;
with Utilities;   use Utilities;
with Model_Data;  use Model_Data;
with Run_Data;    use Run_Data;

package body Generate_Space is
  -- Put the prologue of the dot file
  procedure Put_Prologue is
    S: Global.Line;
    L: Natural;
  begin
    Put_Line(DOT_File, "digraph """ & """ {");
    begin
      -- If there is a prologue file, write its contents to the dot file
      Open(Prologue_File, In_File, File_Root.all & Prologue_Extension);
      while not End_Of_File(Prologue_File) loop
        Get_Line(Prologue_File, S, L);
        Put_Line(DOT_File, S(1..L));
      end loop;
      Close(Prologue_File);
    exception
      -- Prologue file doesn't exist, so create a new one
      --   Write the default to both the prologue and the dot files
      when Name_Error =>
        Create(Prologue_File, Out_File,
          File_Root.all & Prologue_Extension);
        for I in Prologue'Range loop
          Put_Line(Prologue_File, Prologue(I));
          Put_Line(DOT_File, Prologue(I));
        end loop;
        Close(Prologue_File);
    end;
  end Put_Prologue;

  -- Format the label of a node with the line numbers and statements
  --   pointed to by the process instruction pointers and with
  --   the values (but not the names) of the variables
  function Format_Label(State: Natural) return String is
    S:       Global.Line; -- Buffer to build the label
    N:       Positive;    -- Index within the buffer
    Src:     Natural;     -- Source state
    T:       Natural;     -- Transition
    V:       Integer;     -- Value

    -- Enter a substring Sub into the string buffer
    procedure Enter(Sub: in String) is
    begin
      S(N..N+Sub'Length-1) := Sub;
      N := N + Sub'Length;
    end Enter;
    
    -- Enter Effect if Condition is true
    procedure Enter_Effect(Condition: in Boolean; Effect: in String) is
    begin
      if Condition then Enter(Effect); end if;
    end Enter_Effect;
    
  begin
    N := 1;
    -- The node name is the state number
    Enter(Natural'Image(State));
    Enter(" [label=""");

    -- Format statements from the transitions in the model
    for I in 0..Processes-1 loop
      -- The state name is a string like like "wantp=1,wantq=0,p=3,q=4,"
      -- Given the process name from the process table,
      --   extract the location counter of the that process
      Src := Extract(State_Table(State).N, "," & Trim(Process_Table(I)));

      -- Search for a transition in the model with the same source
      T := 0;
      loop
        exit when Transition_Table(I, T).Source = Src;
        T := T + 1;
      end loop;

      -- Extract the fields and format them
      declare
        TT:   Transition_Type renames Transition_Table(I, T); 
        Ln:   String := Natural'Image(TT.Line_Number) & ". ";
        Stmt: String := Trim(TT.Statement);
      begin
        if TT.Line_Number /= 0 then
          Enter(Ln);
        end if;
        Enter(Stmt);
        -- For a simulation, search for the transition in the table
        --   of executable transitions and set the effect
        if Simulation then
          for K in reverse 0..State_Table(State).Exec-1 loop
            if State_Table(State).Ex_Array(K) =
              (Process_Table(I), TT.Source, TT.Target) then
                Enter_Effect(True, Exec_Effect);
              exit;
            end if;
          end loop;
        else
          Enter_Effect(TT.End_Label=1,    End_Effect);
          Enter_Effect(TT.Accept_Label=1, Accept_Effect);
        end if;
        Enter("\n");
      end;
    end loop;

    -- Format variable values
    for I in 0..Variables-1 loop
      -- Extract the variable's value from the state name
      V := Extract(State_Table(State).N, Trim(Variable_Table(I)));
      -- For fairness, the copy number is formatted with brackets: [n]
      if Fairness and then I = Variables-1 then
        Enter(" [" & Integer'Image(V) & ']');
      else
        Enter(Integer'Image(V));
      end if;
    end loop;
    Enter("\n""");

    -- Format effects
    Enter_Effect(State_Table(State).Matched, Matched_Effect);
    Enter_Effect(State_Table(State).Current, Current_Effect);
    Enter_Effect(State_Table(State).Stack,   Stack_Effect);
    Enter_Effect(State_Table(State).Error,   Error_Effect);
    Enter_Effect(State_Table(State).Inner,   Inner_Effect);
    -- For a simulation, the number of peripheries is the number
    --   of visits to the state
    if Simulation then
      Enter("peripheries=" & Trim_Int(State_Table(State).Visits));
    end if;
    Enter("];");

    return S(1..N-1);
  end Format_Label;

  -- Put the Count'th dot file
  procedure Put_Dot_File(Count: in Natural) is
    -- The file numbering starts from 000
    -- Compute string Count_Z with leading zeros
    Count_S: String       := Trim(Natural'Image(Count));
    Count_Z: String(1..3) := (1..3-Count_S'Length => '0') & Count_S; 
  begin
    -- Create the dot file and put the prologue to the dot file
    Create(Global.Dot_File, Out_File, 
      Global.File_Root.all & "-" & Count_Z & Global.Dot_Extension);
    Put_Prologue;

    -- Put the states, formatting the label
    for I in 0..States-1 loop
      Put_Line(DOT_File, Format_Label(I));
    end loop;

    -- Put the edges
    for I in 0..Edges-1 loop
      Put(DOT_File,
        Natural'Image(Edge_Table(I).Source) & " ->" &
        Natural'Image(Edge_Table(I).Target));
      Put_Line(DOT_File, ";");
    end loop;

    -- Put the closing brace and close the file
    Put_Line(DOT_File, "}");
    Close(Global.Dot_File);
  end Put_Dot_File;
end Generate_Space;
