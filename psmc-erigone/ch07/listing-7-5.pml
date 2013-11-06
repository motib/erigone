/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

chan request = [0] of { byte, chan };
chan reply [2] = [0] of { byte, byte };

active [2] proctype Server() {
  byte client;
  chan replyChannel;
end: 
  do
  :: request ? client, replyChannel ->
     printf("Client %d processed by server %d\n", client, _pid);
	 replyChannel ! _pid, client;
  od
}

active [2] proctype Client() {
	byte server;
  byte whichClient;
	request ! _pid, reply[_pid-2];
	reply[_pid-2] ? server, whichClient;
	printf("Reply received from server %d by client %d\n", server, _pid);
    assert(whichClient == _pid)
}
