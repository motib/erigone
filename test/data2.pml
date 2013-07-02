byte  a[4];
short b[4];
int   c[4];

active proctype P() {
  a[0] = 1;
  a[1] = a[0] + 5;
  a[2] = a[1] + a[0];
  a[3] = 4;
  a[3]++;
  b[0] = 301;
  b[1] = b[0] + 10;
  b[2] = b[1] + b[0];
  b[3] = 304;
  b[3]--;
  c[0] = 100001;
  c[1] = c[0] + 1;
  c[2] = c[0] + c[1];
  c[3] = 100004;
  c[3]++;
  
  printf("%d %d %d %d\n", a[0], a[1], a[2], a[3]);
  printf("%d %d %d %d\n", b[0], b[1], b[2], b[3]);
  printf("%d %d %d %d\n", c[0], c[1], c[2], c[3]);
}
