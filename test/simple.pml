byte n = 0;
byte finish = 0;
active proctype P() {
  byte temp;
  temp = n;
  n = temp + 1;
  finish++;
}

active proctype Q() {
  byte temp;
  temp = n;
  n = temp + 1;
  finish++;
}

active proctype R() {
  finish == 2;
  assert (n == 2);
}
