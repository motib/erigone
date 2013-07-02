byte sync = 0;
active proctype P() {
  sync == 1;
  printf("pid is %d, nrpr is %d\n", _pid, _nr_pr);
  sync = 2;
}

active proctype Q() {
  sync == 2;
  printf("pid is %d, nrpr is %d\n", _pid, _nr_pr);
}

active proctype R() {
  printf("before pid is %d, nrpr is %d\n", _pid, _nr_pr);
  sync = 1;
  _nr_pr == 1;
  printf("after pid is %d, nrpr is %d\n", _pid, _nr_pr);
}
