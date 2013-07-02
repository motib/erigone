byte sem = 1;
bool csp = false, csq = false;

ltl mutex { [](!csp || !csq) }
ltl liveness { []<>csp }

active proctype p() {	
  do
  :: 
    atomic {
      sem > 0;
      sem--
    }
    csp = true;
    csp = false;
    sem++
  od
}

active proctype q() {	
  do
  :: 
    atomic {
      sem > 0;
      sem--
    }
    csq = true;
    csq = false;
    sem++
  od
}
