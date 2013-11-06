/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
      atomic {
         !wantQ;
         wantP = true
      }
      printf("Critical section P\n");
      wantP = false
  od
}

active proctype Q() {
  do
  ::  printf("Noncritical section Q\n");
      atomic {
         !wantP;
         wantQ = true
      }
      printf("Critical section Q\n");
      wantQ = false
  od
}
