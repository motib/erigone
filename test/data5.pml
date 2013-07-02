hidden byte  t = 200;
hidden short s = 8195;
local int   i = 4194311;
chan ch1 = [2] of { byte, short, int };
chan ch2 = [2] of { byte, short, int };

active proctype P() {
  xs ch1;
  xr ch2;
  byte t1;
  short s1;
  int i1;
  ch1 ! t, s, i;
  ch2 ? t1, s1, i1; 
  printf("%d %d %d\n", t1, s1, i1);
}

active proctype Q() {
  xr ch1;
  xs ch2;
  byte t1;
  short s1;
  int i1;
  ch1 ? t1, s1, i1; 
  printf("%d %d %d\n", t1, s1, i1);
  ch2 ! t/2, s/2, i/2;
}
