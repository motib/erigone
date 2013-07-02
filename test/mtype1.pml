mtype = { request1, request2 };
mtype = { reply1,   reply2, ack, nack };

active proctype p() {
  printf("mtype=%e,value=%d\n", request1, request1); 
  printf("mtype=%e,value=%d\n", request2, request2); 
  printf("mtype=%e,value=%d\n", reply1,   reply1); 
  printf("mtype=%e,value=%d\n", reply2,   reply2); 
  printf("mtype=%e,value=%d\n", ack,      ack); 
  printf("mtype=%e,value=%d\n", nack,     nack); 
}
