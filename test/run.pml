byte sync = 0;

proctype p(byte x; byte y) {
  sync == _pid;
  printf("%d is in p x=%d, y=%d\n", _pid, x, y);
  sync++;
}

proctype q(byte y; byte x) {	
  sync == _pid;
  printf("%d is in q x=%d, y=%d\n", _pid, x, y);
  sync++;
}

init {
  printf("%d init\n", _pid);
  atomic {
    run p(2,3);
    run q(4,5);
    run p(6,7);
    run q(8,9);
  }
  sync = 1;
}
