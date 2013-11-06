/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

byte sem = 1;
byte critical = 0;

active [3] proctype P() {
  do ::
    printf("Non critical section P\n");
    atomic { 
      sem > 0;
      sem-- 
    }
    critical++;
    assert (critical <= 1);
    critical--;
    printf("Critical section P\n");
    sem++
  od
}

