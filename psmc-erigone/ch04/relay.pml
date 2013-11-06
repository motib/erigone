/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: Replace "for" by guarded commands */

byte input, output;
byte i;

active proctype Source() {
  i = 1;
  do
  :: i > 10 -> break
  :: else ->
    input == 0;
    input = i
  od
}

active proctype Relay() {
  do
  :: d_step {
        input != 0;
		output == 0;
        if
        :: output = input
        :: skip
        fi
     }
     input = 0
  od
}

active proctype Destination() {
  do
  :: output != 0;
     printf("Output = %d\n", output);
     output = 0
  od
}
