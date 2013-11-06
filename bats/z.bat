set back=erigone
7z u -r -tzip -x!*\b~*.ad* -x!*\obj\*.ad* c:\%back%\%back%.zip @zlist.bat
copy %back%.zip \zip
copy %back%.zip n:\zip
set back=
pause
