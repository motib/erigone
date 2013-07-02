#define mutex (critical<=1)

bool wantp = false, wantq = false;
byte critical = 0;

ltl { []mutex }

active proctype p() {
    do 
	  :: !wantq;
       wantp = true;
       critical++;
       critical--;
       wantp = false;
    od
}

active proctype q() {
    do 
    :: !wantp;
       wantq = true;
       critical++;
       critical--;
       wantq = false;
    od
}
