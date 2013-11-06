/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: replace int by byte and remove negative numbers */
/* Erigone: replace "for" by guarded commands */
/* Erigone: remove typedef */

byte row[4];
byte col[4];
byte value[4];

active proctype P() {
  byte i = 0;
  byte r = 0;
  byte c;

  row[0] = 0; col[0] = 1; value[0] = 5;
  row[1] = 0; col[1] = 3; value[1] = 8;
  row[2] = 2; col[2] = 0; value[2] = 20;
  row[3] = 3; col[3] = 3; value[3] = 3;

  do
  :: r > 3 -> break
     else ->
       c = 0;
       do
       :: c > 3 -> break
       :: else ->
          if
          :: i == 4 -> printf("0 ")
          :: i < 4 && r == row[i] && c == col[i] ->
               printf("%d ", value[i]);
               i++
          :: else -> printf("0 ")
          fi;
          c++
       od;
       printf("\n");
       r++
  od
}
