/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change int to byte and value from 123 to 120 */

active proctype P() {
  byte value = 120;
  byte reversed;
  reversed = 
    (value % 10) * 100 +
    ((value / 10) % 10) * 10 +
    (value / 100);
  printf("value = %d, reversed = %d\n", value, reversed)
}
