byte x;
bit stop;

ltl { <>(stepper@a) }

active proctype stepper() {
	do
	:: !stop ->
       atomic {
         if 
         :: x < 7 -> 
              x = x + 1
         :: else  ->
              x = 3
         fi
			 }
	:: stop ->
	  a: skip;   /* skip because of bug in Erigone compiler */
	  break
	od
}

active proctype stopper() {
  x >= 3 -> stop = 1
}
