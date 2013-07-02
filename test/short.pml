short a = -5;
short b = 3;

short y1 = a, y2 = b, y3 = 1;

active proctype P() {
  do
  :: y2 == 0 -> break
  :: y2 != 0 && y2 % 2 == 0 ->
       y1 = y1 * y1;
       y2 = y2 / 2
  :: y2 % 2 == 1 -> 
       y2 = y2 - 1;
       y3 = y1 * y3
  od;
  printf("%d to the power %d is %d\n", a, b, y3)
}
