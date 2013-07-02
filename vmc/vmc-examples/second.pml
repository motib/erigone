bool wantp = false, wantq = false;

active proctype p() {
    do 
    ::
       !wantq;
       wantp = true;
       assert(
         !wantp || !wantq);
       wantp = false;
    od
}

active proctype q() {
    do 
    ::
       !wantp;
       wantq = true;
       assert(
         !wantp || !wantq);
       wantq = false;
    od
}
