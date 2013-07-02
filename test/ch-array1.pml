byte a, b;
chan ch1    = [3] of { byte, byte};
chan ch2[2] = [2] of { byte, byte};

active proctype p() {
  ch1    ! 1, 2;
  ch2[0] ! 7, 8;
  ch2[1] ! 9, 10;
  ch1    ! 3, 4;
  ch1    ! 5, 6;

  ch1    ? a, b;
  printf("%d %d \n", a, b);
  ch1    ? a, b;
  printf("%d %d\n", a, b);
  ch1    ? a, b;
  printf("%d %d\n", a, b);
  ch2[0] ? a, b;
  printf("%d %d \n", a, b);
  ch2[1] ? a, b;
  printf("%d %d\n", a, b);
}
