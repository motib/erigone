byte n = 6;
byte proc = 0;

active[3] proctype P() {
  byte t = 5;
  byte u = t + 4;
  proc == _pid;
  printf("%d %d %d\n", n, t, u);
  t = n;
  t = t + _pid;
  u = t * n;
  printf("%d %d %d\n", n, t, u);
  proc++;
}
