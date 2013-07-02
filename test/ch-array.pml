byte a, b, c;
chan chvar;
chan ch[2] = [2] of { byte, byte, byte};

active proctype p() {
  ch[0] ! 1, 2, 3;
  ch[1] ! 4, 5, 6;
  ch[0] ! 7, 8, 9;
  ch[1] ! 10, 11, 12;

  ch[0] ? a, b, c;
  printf("%d %d %d\n", a, b, c);
  ch[0] ? a, b, c;
  printf("%d %d %d\n", a, b, c);
  ch[1] ? a, b, c;
  printf("%d %d %d\n", a, b, c);
  ch[1] ? a, b, c;
  printf("%d %d %d\n", a, b, c);

  chvar = ch[1];
  chvar ! 13, 14, 15;
  chvar = ch[0];
  chvar ! 16, 17, 18;

  ch[0] ? a, b, c;
  printf("%d %d %d\n", a, b, c);
  ch[1] ? a, b, c;
  printf("%d %d %d\n", a, b, c);
}
