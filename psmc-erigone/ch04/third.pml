/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

bool wantP = false, wantQ = false;
byte critical = 0;

active proctype P() {
    do
    ::
		printf("Non critical section P\n");
        wantP = true;
        wantQ == false;
		critical++;
		assert (critical <= 1);
		critical--;
		printf("Critical section P\n");
        wantP = false
	od
}

active proctype Q() {	
	do 
	:: 	
		printf("Non critical section Q\n");
           wantQ = true;
           wantP == false;
		critical++;
		assert (critical <= 1);
		critical--;
		   printf("Critical section Q\n");
           wantQ = false
	od
}
