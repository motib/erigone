/*
  Satisfiable set of clauses
  Run with:
    Options/Limits/Total steps = 50000
    Options/Limits/Progress steps = 100
  On line 37 changed a to !a.
    Terminates unsuccessfully after 22180989 steps
  (Unsatisfiable terminated after 27262972 steps)
*/

active proctype sat() {
	bool a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s;
	bool result;

	if :: a = true :: a = false fi;
	if :: b = true :: b = false fi;
	if :: c = true :: c = false fi;
	if :: d = true :: d = false fi;
	if :: e = true :: e = false fi;
	if :: f = true :: f = false fi;
	if :: g = true :: g = false fi;
	if :: h = true :: h = false fi;
	if :: i = true :: i = false fi;
	if :: j = true :: j = false fi;
	if :: k = true :: k = false fi;
	if :: l = true :: l = false fi;
	if :: m = true :: m = false fi;
	if :: n = true :: n = false fi;
	if :: o = true :: o = false fi;
	if :: p = true :: p = false fi;
	if :: q = true :: q = false fi;
	if :: r = true :: r = false fi;
	if :: s = true :: s = false fi;

	result =
	(!a || !b ||  c ||  d ||  e) &&
	(!a ||  b || !c ||  d ||  e) &&
	(!a || !b || !c ||  d ||  e) &&
	(!a ||  b ||  c || !d ||  e);
  result = result &&
	( a || !b ||  c || !d ||  e) &&
	( a ||  b || !c || !d ||  e) &&
	(!a || !b || !c || !d ||  e) &&
	(!a ||  b ||  c ||  d || !e);
  result = result &&
	( a || !b ||  c ||  d || !e) &&
	( a ||  b || !c ||  d || !e) &&
	(!a || !b || !c ||  d || !e) &&
	( a ||  b ||  c || !d || !e);
  result = result &&
	(!a || !b ||  c || !d || !e) &&
	(!a ||  b || !c || !d || !e) &&
	( a || !b || !c || !d || !e) &&
	( a ||  b ||  c ||  d ||  e);
  result = result &&
	(!f ||  g ||  h ||  i ||  j) &&
	( f || !g ||  h ||  i ||  j) &&
	( f ||  g || !h ||  i ||  j) &&
	(!f || !g || !h ||  i ||  j);
  result = result &&
	( f ||  g ||  h || !i ||  j) &&
	(!f || !g ||  h || !i ||  j) &&
	(!f ||  g || !h || !i ||  j) &&
	( f || !g || !h || !i ||  j);
  result = result &&
	( f ||  g ||  h ||  i || !j) &&
	(!f || !g ||  h ||  i || !j) &&
	(!f ||  g || !h ||  i || !j) &&
	( f || !g || !h ||  i || !j);
  result = result &&
	(!f ||  g ||  h || !i || !j) &&
	( f || !g ||  h || !i || !j) &&
	( f ||  g || !h || !i || !j) &&
	(!f || !g || !h || !i || !j);
  result = result &&
	(!k ||  l ||  m ||  n ||  o) &&
	( k || !l ||  m ||  n ||  o) &&
	( k ||  l || !m ||  n ||  o) &&
	(!k || !l || !m ||  n ||  o);
  result = result &&
	( k ||  l ||  m || !n ||  o) &&
	(!k || !l ||  m || !n ||  o) &&
	(!k ||  l || !m || !n ||  o) &&
	( k || !l || !m || !n ||  o);
  result = result &&
	( k ||  l ||  m ||  n || !o) &&
	(!k || !l ||  m ||  n || !o) &&
	(!k ||  l || !m ||  n || !o) &&
	( k || !l || !m ||  n || !o);
  result = result &&
	(!k ||  l ||  m || !n || !o) &&
	( k || !l ||  m || !n || !o) &&
	( k ||  l || !m || !n || !o) &&
	(!k || !l || !m || !n || !o);
  result = result &&
	(!p ||  q ||  r ||  s) &&
	( p || !q ||  r ||  s) &&
	( p ||  q || !r ||  s) &&
	(!p || !q || !r ||  s);
  result = result &&
	( p ||  q ||  r || !s) &&
	(!p || !q ||  r || !s) &&
	(!p ||  q || !r || !s) &&
	( p || !q || !r || !s);
  result = result &&
	(!a ||  f ||  k ||  p) &&
	( a || !f ||  k ||  p) &&
	( a ||  f || !k ||  p) &&
	(!a || !f || !k ||  p);
  result = result &&
	( a ||  f ||  k || !p) &&
	(!a || !f ||  k || !p) &&
	(!a ||  f || !k || !p) &&
	( a || !f || !k || !p);
  result = result &&
	(!b ||  g ||  l ||  q) &&
	( b || !g ||  l ||  q) &&
	( b ||  g || !l ||  q) &&
	(!b || !g || !l ||  q);
  result = result &&
	( b ||  g ||  l || !q) &&
	(!b || !g ||  l || !q) &&
	(!b ||  g || !l || !q) &&
	( b || !g || !l || !q);
  result = result &&
	(!c ||  h ||  m ||  r) &&
	( c || !h ||  m ||  r) &&
	( c ||  h || !m ||  r) &&
	(!c || !h || !m ||  r);
  result = result &&
	( c ||  h ||  m || !r) &&
	(!c || !h ||  m || !r) &&
	(!c ||  h || !m || !r) &&
	( c || !h || !m || !r);
  result = result &&
	(!d ||  i ||  n ||  s) &&
	( d || !i ||  n ||  s) &&
	( d ||  i || !n ||  s) &&
	(!d || !i || !n ||  s);
  result = result &&
	( d ||  i ||  n || !s) &&
	(!d || !i ||  n || !s) &&
	(!d ||  i || !n || !s) &&
	( d || !i || !n || !s);
  result = result &&
	(!e ||  j ||  o) &&
	( e || !j ||  o) &&
	( e ||  j || !o) &&
	(!e || !j || !o);
	assert(!result)
}
