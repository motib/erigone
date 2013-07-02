-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
-- Expand a formula into a tableau
--   The algorithm is explained in:
--     Gerth, Peled, Vardi, Wolper (GPVW)
--     Simple on-the-fly automatic verification of linear temporal logic
--     Proceedings of the Fifteenth IFIP WG6.1 International Symposium
--     on Protocol Specification, Testing and Verification XV, 1996
--   and in
--     Kroeger, Merz
--     Temporal Logic and State Systems, Springer, 2008
--
private package LTL.Nodes is
  -- Construct the tableau for formula F
  --   Return the set of nodes in the tableau
  function Construct_Tableau(F: Formula_Ptr) return Node_Sets.Set;
end LTL.Nodes;
