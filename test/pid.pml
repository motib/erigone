pid procs = 0;

active[2] proctype p() {
  procs == _pid;
  printf("%d is in p's critical section\n", _pid);
  procs++;
}

active[3] proctype q() {	
  procs == _pid;
  printf("%d is in q's critical section\n", _pid);
  procs++;
}

init {
  printf("%d init proc\n", _pid);
  procs = 1;
}
