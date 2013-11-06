/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change byte to int replace conditional expression */

active proctype P() {
	byte a = 5, b = 5, max;
	if
	:: a >= b -> max = a;
	:: b >= a -> max = b+1;
	fi;
	assert ((a >= b && max == a) || (a <  b && max == b));
}
