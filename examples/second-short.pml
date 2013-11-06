bool wantp = false, wantq = false;

active proctype p() {
    do 
    ::
       !wantq;
       wantp = true;
       wantp = false;
    od
}

active proctype q() {
    do 
    ::
       !wantp;
       wantq = true;
       wantq = false;
    od
}
