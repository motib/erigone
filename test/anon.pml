chan ch1 = [2] of { byte, byte, byte};
byte a, b, c;

active proctype p() {
  ch1 ! 1, 2, 3;
  ch1 ! 4, 5, 6;
}

active proctype q() {
  ch1 ? a, b, c;
  printf("%d %d %d\n", a, b, c);
  _ = a;
  ch1 ? a, _, c;
  printf("%d %d %d\n", a, b, c);
}
