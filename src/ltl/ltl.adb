-- Copyright 2008-12 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Text_IO; use Ada.Text_IO;
with Files, Global, LTL.Formulas, LTL.Nodes, LTL.Automaton, Options;
package body LTL is
  -- Check equality of formulas by structural recursion
  function Equals(Left, Right: Formula_Ptr) return Boolean is
  begin
    if Left = null and Right = null then
      return True;
    elsif (Left = null  and Right /= null) or
          (Left /= null and Right = null)  then
      return False;
    elsif Left.Token /= Right.Token then
      return False;
    elsif (Left.Token = Atomic and Right.Token = Atomic) then
      return Left.Ident = Right.Ident;
    else
      return Equals(Left.Left,  Right.Left) and
             Equals(Left.Right, Right.Right);
    end if;
  end Equals;

  -- Check less-than relation of formulas by structural recursion
  function Less_Than(Left, Right: Formula_Ptr) return Boolean is
  begin
    if Left = null and Right = null then
      return False;
    elsif (Left = null  and Right /= null) then
      return True;
    elsif (Left /= null and Right = null)  then
      return False;
    elsif Left.Token < Right.Token then
      return True;
    elsif (Left.Token = Atomic and Right.Token = Atomic) then
      return Left.Ident < Right.Ident;
    else
      return Less_Than(Left.Left,  Right.Left) or else
             (Equals(Left.Left,  Right.Left) and 
             Less_Than(Left.Right, Right.Right));
    end if;
  end Less_Than;

  -- Equality of nodes by the node name
  function "="(Left, Right: Node) return Boolean is
  begin
    return Left.N = Right.N;
  end "=";

  -- Less than of nodes by the node name
  function "<"(Left, Right: Node) return Boolean is
  begin
    return Left.N < Right.N;
  end "<";

  -- Read an LTL formula from a file and return an array of transitions
  function LTL_To_Automaton return Automata.Transition_Array is
    use Ada.Text_IO;
    use type Options.LTL_Type;

    -- The transition array constructed from the tableau
    LTL_Transitions: Automata.Transition_Array(Byte);
    LTL_File:        File_Type;      -- File with LTL formula
    Count:           Byte;           -- Count of the transitions
    F:               Formula_Ptr;    -- Formula constructed from the input
    N:               Node_Sets.Set;  -- The constructed tableau
    S:               Global.Line;    -- Buffer for reading formula
    L:               Natural := 1;
  begin
    -- If "-tname" or "-t" and no unnamed internal ltl,
    --   open the files "name.prp" or "filename.prp"
    if Options.LTL_Mode = Options.File or else
        (Options.LTL_Mode = Options.Default_LTL and then
        Files.LTL_Buffer = null) then
      Open(LTL_File, In_File, Files.LTL_File_Name.all);
      while not End_Of_File(LTL_File) loop
        Get_Line(LTL_File, S(L..S'Last), L);
        L := L + 1;
      end loop;
      Files.LTL_Buffer := new String'(S(1..L-1));
    end if;

    -- Construct a Formula from the string
    F := LTL.Formulas.To_Formula(Files.LTL_Buffer.all);
    if Options.Display(Options.LTL) then
      Put("ltl formula=");
      LTL.Formulas.Put_Formula(F);
      Put_Line(",");
    end if;

    -- Push negation inward
    F := LTL.Formulas.Push_Negation(F);
    if Options.Display(Options.LTL) then
      Put("push negation=");
      LTL.Formulas.Put_Formula(F);
      Put_Line(",");
    end if;

    -- Construct the tableau
    N := LTL.Nodes.Construct_Tableau(F);

    -- Extract the states and transitions from the tableau
    LTL.Automaton.Convert(N, LTL_Transitions, Count);

    -- Return just the slice with the transitions
    return LTL_Transitions(0..Count-1);
  exception
    when Name_Error =>
      raise File_Error
        with "LTL file not found """ & Files.LTL_File_Name.all & """";
  end LTL_To_Automaton;
end LTL;
