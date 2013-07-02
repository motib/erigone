#define add(x,y) (x+y)

byte  t = 200;
short s = 8195;
int   i = 4194311;

active proctype P() {
  printf("%d %d %d\n", t, s, i);
  s = s - t;
  i = add(s,t) * add(s,t);
  printf("%d %d %d\n", t, s, i);
  t++;
  s--;
  i++;
  printf("%d %d %d\n", t, s, i);
}
