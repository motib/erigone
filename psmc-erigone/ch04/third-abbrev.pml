/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

bool wantP = false, wantQ = false;

active proctype P() {
  do ::  wantP = true; 
          !wantQ;
          wantP = false
  od
}

active proctype Q() {
  do ::  wantQ = true;
          !wantP;
          wantQ = false
  od
}
