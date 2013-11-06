/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change int to byte */

active proctype P() {
	byte a = 5, b = 5;
	byte max;
	byte branch;
	if
	:: a >= b -> max = a; branch = 1;
	:: b >= a -> max = b; branch = 2;
	fi;
	printf("The maximum of %d and %d = %d by branch %d\n",
			a, b, max, branch);
}
