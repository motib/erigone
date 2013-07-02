-- Copyright 2008-12 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Translate a LTL formula into a Buchi automaton.
--
with Ada.Containers.Ordered_Sets;
with Automata;
with Global; use Global;
package LTL is
  -- Read an LTL formula from a file and return an array of transitions
  function LTL_To_Automaton return Automata.Transition_Array;
private
  -- Types for atomic formulas and operators in a formula
  type Tokens is (Atomic, Negation, Always, Eventually,
                  Conjunction, Disjunction, Implication,
                  Equivalence, Until_Op, Weak_Until_Op, Dual_Until_Op);

  -- Formulas are represented as pointers to binary trees
  type Formula;
  type Formula_Ptr is access Formula;
  type Formula is
    record
      Token: Tokens;       -- Operator or atomic formula
      Ident: Name;         -- Identifier for atomic formula
      Left:  Formula_Ptr;  -- Null for atomic and unary formula
      Right: Formula_Ptr;  -- Right or only subformula
    end record;

  -- Ordered sets need these functions
  -- Less_Than takes into account the ordering of type Tokens
  function Less_Than(Left, Right: Formula_Ptr) return Boolean;
  function Equals   (Left, Right: Formula_Ptr) return Boolean;

  -- Ordered sets of formulas
  package Formula_Sets is
    new Ada.Containers.Ordered_Sets(Formula_Ptr, Less_Than, Equals);

  -- Names of nodes are of type Byte
  -- Sets of names are ordered sets
  package Name_Sets is new Ada.Containers.Ordered_Sets(Byte);

  -- Node type using notation of GPVW
  type Node is
    record
      N:        Byte;
      Incoming: Name_Sets.Set;
      NewF:     Formula_Sets.Set;
      OldF:     Formula_Sets.Set;
      Next:     Formula_Sets.Set;
    end record;

  -- Functions needed for an ordered set; they compare node names
  function "="(Left, Right: Node) return Boolean;
  function "<"(Left, Right: Node) return Boolean;

  -- A set of Nodes is an ordered set
  package Node_Sets is new Ada.Containers.Ordered_Sets(Node);
end LTL;
