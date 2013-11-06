/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: replace "for" by guarded commands */
/* Erigone: Replace int by byte */
/* Erigone: move all declarations to start of proctype */

active proctype P() {
	byte a[5];
  byte i = 0;
	byte sum = 0;
	a[0] = 0; a[1] = 10; a[2] = 20; a[3] = 30; a[4] = 40;
	
	do
    :: i > 4 -> break
    :: else   ->
        sum = sum + a[i];
        i++
    od;
	printf("The sum of the numbers = %d\n", sum);
}
