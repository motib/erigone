/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change int to byte and replace #define by a variable */

active proctype P() {
	byte N = 10;
	byte sum = 0;
	
	byte i; 
	i = 1; 
	do 
	:: i > N -> break 
	:: else ->
		sum = sum + i;
		i++
	od;
	printf("The sum of the first %d numbers = %d\n", N, sum);
}
