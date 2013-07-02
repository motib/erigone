byte n = 0;
byte finish = 0;

active[3] proctype P() {
  byte temp;
  temp = n;
  n = temp + 1;
  finish++;
}

active proctype R() {
  finish == 3;
  assert (n > 2);
}
