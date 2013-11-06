/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change int to byte and b=-4 to b=4 */

active proctype P() {
	byte a = 1, b = 4, c = 4;
	byte disc;
	disc = b * b - 4 * a * c;
	if
	:: disc < 0  -> printf("disc = %d: no real roots\n", disc)
	:: disc == 0 -> printf("disc = %d: duplicate real roots\n", disc)
	:: disc > 0  -> printf("disc = %d: two real roots\n", disc)
	fi
}
