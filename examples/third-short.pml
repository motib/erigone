bool wantp = false, wantq = false;
active proctype p() {
    do 
    ::
      wantp = true;
      !wantq;
      wantp = false;
    od
}

active proctype q() {
    do 
    ::
      wantq = true;
      !wantp;
      wantq = false;
    od
}

