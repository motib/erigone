/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

chan request = [4] of { byte };
chan reply = [4] of { byte, byte };

active [2] proctype Server() {
  byte client;
end:
  do
  :: request ? client ->
     printf("Client %d processed by server %d\n", client, _pid);
     reply ! _pid, client
  od
}

active [4] proctype Client() {
  byte server;
  request ! _pid;
  reply ?? server, eval(_pid);
  printf("Reply received from server %d by client %d\n", server, _pid)
}
