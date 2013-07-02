bit aktiv[2];
bit last;
bit crit[2];

ltl { []<>crit[0] && []<>crit[1] }

proctype threadMX (bit self) {
	do
	:: break
	:: aktiv[self] = 1;
	   last = self ;
	   (last == 1-self || ! aktiv[1-self]); 
	   crit[self] = 1 ;
	   crit[self] = 0 ;
     aktiv[self] = 0 
	od
}

init {
  atomic {
    run threadMX (0) ;
    run threadMX (1) ;
  }
}
