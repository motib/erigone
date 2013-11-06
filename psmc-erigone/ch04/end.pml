/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

byte request = 0;

active proctype Server1() {
  do
  :: request == 1 -> 
         printf("Service 1\n"); 
         request = 0;
  od
}

active proctype Server2() {	
  do 
  :: request == 2 -> 
         printf("Service 2\n"); 
         request = 0;
  od
}

active proctype Client() {
  request = 1;
  request == 0;
  request = 2;
  request == 0;
}
