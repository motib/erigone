/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

mtype { red, yellow, green };
chan ch = [0] of { mtype, byte, bool };

active proctype Sender() {
  ch ! red, 20, false;
  printf("Sent message\n")
}

active proctype Receiver() {
  mtype color;
  byte time;
  bool flash;
  ch ? color, time, flash;
  printf("Received message %e, %d, %d\n", color, time, flash)
}
