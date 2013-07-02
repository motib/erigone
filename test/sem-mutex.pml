byte sem = 1;
bool csp = false, csq = false;

ltl { [](!csp || !csq) }

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
