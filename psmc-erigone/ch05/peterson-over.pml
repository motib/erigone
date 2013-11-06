/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: change defined proposition to use ## workaround */

bool    wantP, wantQ;
byte    last = 1;

active proctype P() {
    do
    ::  wantP = true;
		last = 1;
try:    (wantQ == false) || (last == 2);
cs:     wantP = false
    od
}

active proctype Q() {
    do
    ::  wantQ = true;
		last = 2;
try:    (wantP == false) || (last == 1);
cs:     wantQ = false
    od
}
