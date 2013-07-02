-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
-- LTL formulas
--
private package LTL.Formulas is
  -- Display a formula
  procedure Put_Formula(F: in Formula_Ptr);

  -- Display a set of formulas
  procedure Put_Formula_Set(F_Set: in Formula_Sets.Set);

  -- Compile a string to a formula
  function  To_Formula(S: String) return Formula_Ptr;

  -- Push negations inwards
  function  Push_Negation(F: Formula_Ptr) return Formula_Ptr;

  -- Check for a contradiction
  function  Contradiction(Left, Right: Formula_Ptr) return Boolean;

  -- Return the string representation of a literal
  function  Get_Literal(F: Formula_Ptr) return Global.Name;

  -- Decompose a formula F into sets of subformulas New1, New2
  -- For temporal operators,
  --   there is a set that must be true in the Next node
  procedure Decompose(
    F: in Formula_Ptr; New1, New2, Next: out Formula_Sets.Set);
end LTL.Formulas;
