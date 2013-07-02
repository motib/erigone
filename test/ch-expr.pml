byte a, b, c;
chan ch = [3] of { byte, byte, byte};

active proctype p() {
  printf("len=%d,empty=%d,nempty=%d,full=%d,nfull=%d,\n",
    len(ch), empty(ch), nempty(ch), full(ch), nfull(ch));
  ch !  1, 2, 3;
  printf("len=%d,empty=%d,nempty=%d,full=%d,nfull=%d,\n",
    len(ch), empty(ch), nempty(ch), full(ch), nfull(ch));
  ch !  4, 5, 6;
  printf("len=%d,empty=%d,nempty=%d,full=%d,nfull=%d,\n",
    len(ch), empty(ch), nempty(ch), full(ch), nfull(ch));
  ch !  7, 8, 9;
  printf("len=%d,empty=%d,nempty=%d,full=%d,nfull=%d,\n",
    len(ch), empty(ch), nempty(ch), full(ch), nfull(ch));
  ch ?  a, b, c;
  printf("len=%d,empty=%d,nempty=%d,full=%d,nfull=%d,\n",
    len(ch), empty(ch), nempty(ch), full(ch), nfull(ch));
  ch ?  a, b, c;
  printf("len=%d,empty=%d,nempty=%d,full=%d,nfull=%d,\n",
    len(ch), empty(ch), nempty(ch), full(ch), nfull(ch));
  ch ?  a, b, c;
  printf("len=%d,empty=%d,nempty=%d,full=%d,nfull=%d,\n",
    len(ch), empty(ch), nempty(ch), full(ch), nfull(ch));
}
