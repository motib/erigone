/* Copyright (C) 2006 M. Ben-Ari. See copyright.txt */
/* 
   Merge sort
   Run on initial data in process init
*/

byte a[8], result[8];
byte s[2] = 0;

/* Insertion sort of each half of the array */
proctype Sort (byte sem; byte low; byte high) {
	byte max, temp, I, J;
	I = low;
	do :: I > high-1 -> break
	   :: else ->
		max = I;
		J = I+1;
		do :: J > high -> break
		   :: else ->
			if :: a[J] < a[max] -> max = J :: else fi; 
		  J++
		od;
		temp = a[I]; a[I] = a[max]; a[max] = temp;
		I++
	od;
	s[sem]++
}

proctype Merge() {
  byte K;
	byte first, second, r;
  atomic { s[0] > 0; s[0]-- }
	atomic { s[1] > 0; s[1]-- }
	first = 0;
	second = 8 / 2;
	r = 0;
	do
	:: (first >= 8/2) && (second >= 8) -> break
	:: (first >= 8/2) && (second < 8) -> 
		result[r] = a[second]; 	r++; 	second++;
	:: (first < 8/2) && (second >= 8) -> 
		result[r] = a[first]; 	r++; 	first++;
	:: (first < 8/2) && (second < 8) -> 
		if 
		:: a[first] < a[second] -> 
		result[r] = a[first]; 	r++; 	first++;
		:: else ->
		 result[r] = a[second]; 	r++; 	second++;
		fi
	od;
	K = 0;
	do 
	:: K >= 8-2 -> break
	:: else ->
	  assert(result[K] < result[K+1]);
		printf(" %d\n", result[K]);
	  K++
	od;
	printf(" %d\n", result[8-1])
}

init {
	atomic {
		a[0] = 5; a[1] = 1; a[2] = 10; a[3] = 7;
		a[4] = 4; a[5] = 3; a[6] = 12; a[7] = 8;
		run Sort(0, 0, 3);
		run Sort(1, 4, 7);
		run Merge();
	}
}

