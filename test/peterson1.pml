bit aktiv[2];
bit last;
bit crit;

proctype threadMX (bit self) {
	do
	:: break
	:: aktiv[self] = 1;
	   last = self ;
	   (last == 1-self || ! aktiv[1-self]); 
       assert crit == 0 ;
	   crit = 1 ;
	   crit = 0 ;
       aktiv[self] = 0 
	od
}

init {
  atomic {
    run threadMX (0) ;
    run threadMX (1) ;
  }
}
