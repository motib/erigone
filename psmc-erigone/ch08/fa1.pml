/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: replace timeout by else */
/* Erigone: replace defined identifier by a literal */
/* Erigone: remove inline */

active proctype FA() {
  byte h;
  byte i[5];
  if :: i[0] = 'a' :: i[0] = 'b' :: i[0] = 'c' fi
  if :: i[1] = 'a' :: i[1] = 'b' :: i[1] = 'c' fi
  if :: i[2] = 'a' :: i[2] = 'b' :: i[2] = 'c' fi
  if :: i[3] = 'a' :: i[3] = 'b' :: i[3] = 'c' fi
  i[4] = '.';
q0: if
    :: i[h] == 'a'  -> h++; goto q0;
    :: i[h] == 'b'  -> h++; goto q3;
    :: i[h] == 'b'  -> h++; goto q1
    :: else -> goto reject
    fi;
q1: if
    :: i[h] == 'b'  -> h++; goto q2
    :: else -> goto reject
    fi;
q2: if
    :: i[h] == 'b'  -> h++; goto q1;
    :: i[h] == '.'  -> goto accept
    :: else -> goto reject
    fi;
q3: if
    :: i[h] == 'c'  -> h++; goto q3;
    :: i[h] == '.'  -> goto accept
    :: else -> goto reject
    fi;
accept: 
    printf("Accepted!\n");
	  assert(false);
reject:
    printf("Rejected ...\n")
}
