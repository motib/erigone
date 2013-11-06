/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

active proctype P() {
	bool a, b, c;
	bool result;

	if :: a = true :: a = false fi;
	if :: b = true :: b = false fi;
	if :: c = true :: c = false fi;

	result = 
		(a || c)  && (!a || !c) &&
		(a || !b) && (!a || b)  &&
		(b || !c) && (!b || !c);

	printf("a = %d, b = %d, c =%d\n", a, b, c);
	printf("Result = %d\n", result);
	assert(!result)
}
