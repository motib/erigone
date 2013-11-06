/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: replace "for" by guarded commands */

chan ch = [0] of { byte };

active proctype Producer() {
  byte n, i;
  i = 1;
  do
  :: i > 10 -> break
  :: else ->
    if
    :: ch ! 0
    :: ch ! 10
    :: ch ! 20
    fi;
    i++
  od
}

active proctype Consumer() {
  byte n;
end:
  do
  :: ch ? n -> printf("%d\n", n)
  od
}
