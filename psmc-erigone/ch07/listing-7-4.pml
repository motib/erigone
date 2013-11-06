/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

chan request = [0] of { byte };
chan reply = [0] of { byte };

active [2] proctype Server() {
	byte client;
end:
	do
    ::  request ? client -> 
			printf("Client %d processed by server %d\n", client, _pid);
			reply ! _pid
	od
}

active [2] proctype Client() {
	byte server;
	request ! _pid;
	reply ? server;
	printf("Reply received from server %d by client %d\n", server, _pid)
}
