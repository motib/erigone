cd src
if "%1"=="e" gnatmake -Perigone    -g %2 %3
if "%1"=="c" gnatmake -Pcompiler   -g %2 %3
if "%1"=="l" cd ..\list
if "%1"=="l" gnatmake -Plist       -g %2 %3
if "%1"=="t" cd ..\trace
if "%1"=="t" gnatmake -Ptrace       -g %2 %3
if "%1"=="v" cd ..\vmc
if "%1"=="v" gnatmake -Pvmc       -g %2 %3
cd ..

