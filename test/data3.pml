byte a[3];
short b[3];
int c[3];
chan ch = [3] of { byte, short, int };
byte x;
short y;
int z;

active proctype P() {
  a[0] = 1;
  a[1] = 2;
  a[2] = 3;
  b[0] = 301;
  b[1] = 302;
  b[2] = 303;
  c[0] = 100001;
  c[1] = 100002;
  c[2] = 100003;
  printf("%d %d %d\n", a[0], a[1], a[2]);
  printf("%d %d %d\n", b[0], b[1], b[2]);
  printf("%d %d %d\n", c[0], c[1], c[2]);
  ch ! a[0], b[0], c[0];
  ch ! a[2], b[2], c[2];
  ch !! a[1], b[1], c[1];
  ch ? x, y, z;
  printf("%d %d %d\n", x, y, z);
  ch ! a[0], b[1], c[2];
  ch ? x, y, z;
  printf("%d %d %d\n", x, y, z);
  ch ? x, y, z;
  printf("%d %d %d\n", x, y, z);
  ch ? x, y, z;
  printf("%d %d %d\n", x, y, z);
}
