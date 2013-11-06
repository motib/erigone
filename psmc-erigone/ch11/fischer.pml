/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

byte turn  = 0;
byte timer[6] = 0;
byte critical = 0;
byte i;

active [6] proctype P() {
start:
  do
  ::  atomic {
        turn == 0 -> timer[_pid] = 2;
        printf("Process %d checks turn==0, timer = %d\n", _pid+1, timer[_pid])
      }
      atomic {
        if
        :: timer > 0 ->
             turn = _pid+1;
             timer[_pid] = 2;
             printf("Process %d sets turn=%d, timer = %d\n", _pid+1, _pid+1, timer[_pid])
        :: else -> goto start
        fi
      }
      atomic {
        timer[_pid] == 0 ->
          if
          ::  (turn == _pid+1) -> critical++;
              printf("Process %d in CS, timer = %d\n", _pid+1, timer[_pid])
          ::  else -> goto start
          fi
      }
      atomic {
        assert (critical <= 1);
        critical--;
        turn = 0
      }
  od
}

active proctype Clock() {
  do
  :: d_step { 
       i = 0;
       do
       :: i >= 6 -> break
       :: else -> 
          if
          :: timer[i] > 0 -> timer[i]--;
	        printf("Timer of process %d ticked, timer = %d\n", i+1, timer[i])
          :: else
          fi;
          i++
       od
     }
  od
}
