byte sem = 0;
byte proc = 0;

active proctype p() {	
end:
  do :: 
    atomic {
      sem > 0;
      sem--
    }
  od
}

active proctype q() {	
end:
  do :: 
    atomic {
      sem > 0;
      sem--
    }
  od
}

active proctype r() {
  printf("number of processes=%d\n", _nr_pr);
  proc = 1;
}

active proctype s() {
  proc == 1;
  printf("number of processes=%d\n", _nr_pr);
}
