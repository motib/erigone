/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: use one mtype declaration for all symbols */

mtype = { red, yellow, green, green_and_yellow, yellow_and_red };

mtype light = green;

active proctype P() {
	do
	::	if
		:: light == red -> light = yellow_and_red
		:: light == yellow_and_red -> light = green
		:: light == green -> light = green_and_yellow
		:: light == green_and_yellow -> light = red
		fi;
		printf("The light is now %e\n", light)
	od
}

