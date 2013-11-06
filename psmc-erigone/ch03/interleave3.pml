byte    n = 0;

active [2] proctype P() {
	byte temp;
	temp = n + 1;
  n = temp;
	printf("Process P%d, n = %d\n", _pid, n);
}
