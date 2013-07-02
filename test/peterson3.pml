bit aktiv[2];
bit last;
bit crit;

ltl { []<>crit }

proctype threadMX (bit self) {
	do
	:: true -> break
	:: aktiv[self] = 1;
	   last = self ;
	   (last == 1-self || ! aktiv[1-self]);
	   if 
	   :: self == 0 -> 
	      crit = 1;
	      crit = 0
	   :: else
	   fi;
     aktiv[self] = 0 
	od
}

init {
  atomic {
    run threadMX (0) ;
    run threadMX (1) ;
  }
}
