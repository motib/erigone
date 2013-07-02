-- Copyright 2009 by  Mordechai (Moti) Ben-Ari. See version.ads
package Expr is
  -- Compile the array selector. A is the table index of the array
  procedure Selector(A: in Integer);

  -- Compile an expression
  procedure Expression;
end Expr;
