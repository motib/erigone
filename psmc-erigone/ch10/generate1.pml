/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: replace "for" by guarded commands */

active proctype Consumer() {
  byte n, i;
  i = 1;
  do
  :: i > 10 -> break
  :: else ->
    if
    :: n = 0
    :: n = 10
    :: n = 20
    fi;
    printf("%d\n", n);
    i++
  od
}
