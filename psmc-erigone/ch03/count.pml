/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Erigone: replace for by guarded commands */

byte    n = 0;

proctype P() {
    byte temp, i;
    i = 1;
    do
    :: i > 10 -> break
    :: else ->
        temp = n;
        n = temp + 1
;
        i++
    od
}

init {
    atomic {
        run P();
        run P()
    }
    (_nr_pr == 1);
    printf("The value is %d\n", n);
    assert (n > 2)
}
