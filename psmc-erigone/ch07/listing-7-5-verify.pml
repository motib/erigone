/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

byte numClients = 0;
chan request = [0] of { byte, chan };
chan reply [3] = [0] of { byte };

active [2] proctype Server() {
	byte client;
	chan replyChannel;
  byte me;
	me = _pid;
end:
	do
    :: 
    request ? client, replyChannel ->
			printf("Client %d sent request   on channel %d, processed by server %d\n",
			       client, replyChannel, me);
			replyChannel ! me
	od
}

active [3] proctype Client() {
	byte server;
	byte me;
	me = _pid-2;
	request ! me, reply[me];
	numClients++;
	assert (numClients <= 2);
	numClients--;
	reply[me] ? server;
	printf("Client %d received reply on channel %d, processed by server %d\n",
	       me, reply[me], server)
}
