/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

chan request = [0] of { byte };

active proctype Server() {
	byte client;
end:
	do
    ::  request ? client -> printf("Client %d\n", client);
	od
}

active proctype Client0() {
	request ! 0;
}

active proctype Client1() {
	request ! 1;
}
