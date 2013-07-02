bool wantp = false, wantq = false;

active proctype p() {
    do 
    ::
       wantp = true;
       !wantq;
       assert(
         !wantp || !wantq);
       wantp = false;
    od
}

active proctype q() {
    do 
    ::
       wantq = true;
       !wantp;
       assert(
         !wantp || !wantq);
       wantq = false;
    od
}
