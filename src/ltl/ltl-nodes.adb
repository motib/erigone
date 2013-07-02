-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO; use Ada.Text_IO;
with LTL.Formulas, Options, Utilities;
package body LTL.Nodes is
  Counter: Byte;   -- Static variable for creating node names

  -- Create a new node name
  function New_Name return Byte is
  begin
    Counter := Counter + 1;
    return Counter;
  end New_Name;

  -- Display a name set
  procedure Put_Name_Set(N: in Name_Sets.Set) is
    procedure Put_Name(Position: in Name_Sets.Cursor) is
    begin
      Utilities.Put(Name_Sets.Element(Position));
    end Put_Name;
  begin -- Put_Name_Set
    Put("{");
    Name_Sets.Iterate(N, Put_Name'Access);
    Put("},");
  end Put_Name_Set;

  -- Display the names of a set of nodes
  procedure Put_Node_Set_Names(N: in Node_Sets.Set) is
    procedure Put_One_Node(Position: in Node_Sets.Cursor) is
    begin
      Utilities.Put(Node_Sets.Element(Position).N);
    end Put_One_Node;
  begin -- Put_Node_Set_Names
    Node_Sets.Iterate(N, Put_One_Node'Access);
  end Put_Node_Set_Names;

  -- Display a node
  procedure Put_Node(N: in Node) is
  begin
    Put("node=");
    Utilities.Put(N.N);
    Put("incoming=");
    Put_Name_Set(N.Incoming);
    Put("new=");
    LTL.Formulas.Put_Formula_Set(N.NewF);
    Put("old=");
    LTL.Formulas.Put_Formula_Set(N.OldF);
    Put("next=");
    LTL.Formulas.Put_Formula_Set(N.Next);
  end Put_Node;

  -- Recursive function to expand the tableau
  function Expand(N: Node; N_Set: Node_Sets.Set) return Node_Sets.Set is
    use Formula_Sets;
    use type Node_Sets.Cursor, Node_Sets.Set, Name_Sets.Set;

    -- Local node and node set variables
    Node1, Node2: Node;
    New_Set:      Node_Sets.Set;
    Cursor_N:     Node_Sets.Cursor;

    -- Local formula and formula set variables
    F:            Formula_Ptr;
    New1, New2, Next1, New_F, Old_F: Formula_Sets.Set;
    Cursor_F:     Formula_Sets.Cursor;

  begin
    if Options.Display(Options.Nodes) then
      Put("expanding=,");
      Put_Node(N);
      Put("with set=");
      if Node_Sets.Is_Empty(N_Set) then
        Put(",");
      else
        Put("{");
        Put_Node_Set_Names(N_Set);
        Put("},");
      end if;
      New_Line;
    end if;

    -- If NewF of node N is empty,
    if Is_Empty(N.NewF) then
      Cursor_N := Node_Sets.First(N_Set);
      -- Search N_Set for ...
      while Cursor_N /= Node_Sets.No_Element loop
        Node1 := Node_Sets.Element(Cursor_N);
        -- ... an existing node with same OldF and Next
        if Node1.OldF = N.OldF and Node1.Next = N.Next then
          -- Add node N's Incoming to the Incoming of the existing node
          Node1.Incoming := Node1.Incoming or N.Incoming;

          if Options.Display(Options.Nodes) then
            Utilities.Put("exists=,node=", Node1.N);
            Put("new incoming=");
            Put_Name_Set(Node1.Incoming);
            New_Line;
          end if;

          -- Create a new node set by replacing Node1 that has been
          --   modified with new Incoming node
          New_Set := N_Set;
          Node_Sets.Replace(New_Set, Node1);
          return New_Set;
        else
          Cursor_N := Node_Sets.Next(Cursor_N);
        end if;
      end loop;

      -- If none, create a new node, move Next to NewF and recurse
      return Expand((
        N        => New_Name,
        Incoming => Name_Sets.To_Set(N.N),
        NewF     => N.Next,
        OldF     => Empty_Set,
        Next     => Empty_Set
        ), Node_Sets.To_Set(N) or N_Set);

    -- Otherwise (N.NewF is non-empty)
    else
      -- Take the first element F of NewF and remove it
      F := First_Element(N.NewF);
      New_F := N.NewF;
      Delete_First(New_F);

      -- F is a literal
      if F.Token = Atomic or F.Token = Negation then
        Cursor_F := First(N.OldF);
        -- Check for a contradiction and discard
        while Cursor_F /= No_Element loop
          if LTL.Formulas.Contradiction(F, Element(Cursor_F)) then
            return N_Set;
          else
            Cursor_F := Next(Cursor_F);
          end if;
        end loop;

        -- Otherwise (not a contradiction), add F to OldF and recurse
        Old_F := N.OldF or To_Set(F);
        return Expand((
          N        => N.N,
          Incoming => N.Incoming,
          NewF     => New_F,
          OldF     => Old_F,
          Next     => N.Next
        ), N_Set);

      -- Conjunctive operator: decompose and recurse once
      elsif F.Token = Conjunction or F.Token = Always then
        LTL.Formulas.Decompose(F, New1, New2, Next1);
        return Expand((
          N        => New_Name,
          Incoming => N.Incoming,
          NewF     => New_F or ((New1 or New2) - N.OldF),
          OldF     => N.OldF or To_Set(F),
          Next     => N.Next or Next1
          ), N_Set);

      -- Disjunctive operator: decompose and recurse twice
      elsif F.Token = Disjunction or F.Token = Eventually or
            F.Token = Until_Op    or F.Token = Weak_Until_Op or
            F.Token = Dual_Until_Op then
        LTL.Formulas.Decompose(F, New1, New2, Next1);
        Node1 := (
          N        => New_Name,
          Incoming => N.Incoming,
          NewF     => New_F or (New1 - N.OldF),
          OldF     => N.OldF or To_Set(F),
          Next     => N.Next);
        Node2 := (
          N        => New_Name,
          Incoming => N.Incoming,
          NewF     => New_F or (New2 - N.OldF),
          OldF     => N.OldF or To_Set(F),
          Next     => N.Next or Next1);
        return Expand(Node2, Expand(Node1, N_Set));
      end if;
    end if;
    return Node_Sets.Empty_Set;
  end Expand;

  -- Construct the tableau for formula F
  --   Return the set of nodes in the tableau
  function Construct_Tableau(F: Formula_Ptr) return Node_Sets.Set is
    N: Node_Sets.Set;
    use Formula_Sets;
  begin
    Counter := 0;
    if Options.Display(Options.Nodes) then
      Put_Line("nodes start=,");
    end if;

    -- Create the initial node and call Expand
    N := Expand((
      N        => New_Name,
      Incoming => Name_Sets.To_Set(0),
      NewF     => To_Set(F),
      OldF     => Empty_Set,
      Next     => Empty_Set
    ), Node_Sets.Empty_Set);

    if Options.Display(Options.Nodes) then
      Put_Line("nodes end=,");
    end if;
    return N;
  end Construct_Tableau;
end LTL.Nodes;
