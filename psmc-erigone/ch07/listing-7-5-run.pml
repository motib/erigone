chan request = [0] of { byte, chan };
chan reply [2] = [0] of { byte, byte };

proctype Server(byte me) {
	byte client;
	chan replyChannel;
end:
	do
    ::  request ? client, replyChannel ->
			printf("Client %d processed by server %d\n", client, me);
			replyChannel ! me, client;
	od
}

proctype Client(byte me; byte myChannel) {
	byte server;
	byte whichClient;
	request ! me, reply[myChannel];
	reply[myChannel] ? server, whichClient;
	printf("Reply received from server %d by client %d\n", server, me);
	assert (whichClient == me);
}

init {
	atomic {
		run Server('s');
		run Server('t');
		run Client('c', 0);
		run Client('d', 1);
	}
}
