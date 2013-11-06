/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */mtype = { red, yellow, green };

mtype light = green;

active proctype P() {
	do
	::	if
		:: light == red -> light = green
		:: light == yellow -> light = red
		:: light == green -> light = yellow
		fi;
		printf("The light is now %e\n", light)
	od
}

