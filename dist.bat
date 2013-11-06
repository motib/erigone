copy src\erigone.exe .
copy trace\trace.exe .
copy list\list.exe .
copy vmc\vmc.exe .
7z u -tzip dist\erigone-%1.zip @distlist.bat
del erigone.exe
del trace.exe
del list.exe
del vmc.exe
7z u -r -tzip -x!src\obj\* -x!.svn\* -x!*.ali -x!*.o dist\erigone-source-%1.zip @distsrclist.bat
7z u -tzip dist\erigone-test-%1.zip @disttestlist.bat
pause
