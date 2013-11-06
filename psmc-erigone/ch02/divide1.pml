/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change byte to int */

active proctype P() {
  byte dividend = 15;
  byte divisor  = 4;
  byte quotient, remainder;

  assert (dividend >= 0 && divisor > 0);

  quotient = 0;
  remainder = dividend;
  do
  :: remainder >= divisor ->
       quotient++;
       remainder = remainder - divisor
  :: else ->
       break
  od;
  printf("%d divided by %d = %d, remainder = %d\n",
         dividend, divisor, quotient, remainder);

  assert (0 <= remainder && remainder < divisor);
  assert (dividend == quotient * divisor + remainder);
}
