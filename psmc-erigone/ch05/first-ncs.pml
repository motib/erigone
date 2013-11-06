/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change defined proposition to use #...# workaround

/* 
   First attempt 
   Simulate non-termination of non-CS
   Verify Safety - invalid end state
*/

byte	turn = 1;

active proctype P() {
	do 
	:: 	
		if 			/* NCS does nothing or halts */
		:: true 
		:: true -> false
		fi;
		(turn == 1);
cs:		turn = 2
	od
}

active proctype Q() {	
	do 
	:: 	
		(turn == 2);
cs:		turn = 1
	od
}
