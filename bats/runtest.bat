set EDIR=test
src\erigone -r %1 %EDIR%\array
src\erigone -r %1 %EDIR%\mergesort

src\erigone -r %1 %EDIR%\data1
src\erigone -r %1 %EDIR%\data2
src\erigone -r %1 %EDIR%\data3
src\erigone -r %1 %EDIR%\data4
src\erigone -r %1 %EDIR%\data5

src\erigone -s %1 %EDIR%\simple
src\erigone -s %1 %EDIR%\simpleactive
src\erigone -s -lt700 %1 %EDIR%\count
src\erigone -s -lt700 %1 %EDIR%\count-run

src\erigone -s %1 %EDIR%\queens
src\erigone -g %1 %EDIR%\queens
src\erigone -s %1 %EDIR%\queens4
src\erigone -g %1 %EDIR%\queens4

src\erigone -s %1 %EDIR%\sat
src\erigone -s -lt20 %1 %EDIR%\sat3

src\erigone -s %1 %EDIR%\fa

src\erigone -s %1 %EDIR%\second-assert
src\erigone -s %1 %EDIR%\third-assert
src\erigone -s %1 %EDIR%\dekker-assert
src\erigone -s %1 %EDIR%\sem-assert
src\erigone -s %1 %EDIR%\sem3

src\erigone -s -t %1 %EDIR%\second-mutex
src\erigone -s -t %1 %EDIR%\second-ltl
src\erigone -s -t %1 %EDIR%\second-rr
src\erigone -s -t %1 %EDIR%\second-def
src\erigone -s -t %1 %EDIR%\dekker-mutex
src\erigone -s -t-mutex %1 %EDIR%\dekker-ltl
src\erigone -s -t %1 %EDIR%\sem-mutex
src\erigone -s -t-mutex %1 %EDIR%\sem-ltl
src\erigone -f -t-liveness %1 %EDIR%\sem-ltl

src\erigone -f -t %1 %EDIR%\fourth-live
src\erigone -f -t %1 %EDIR%\fourth-live
src\erigone -a -t %1 %EDIR%\dekker-live1
src\erigone -a -t %1 %EDIR%\dekker-live2
src\erigone -f -t %1 %EDIR%\dekker-live1
src\erigone -f -t -lt40 %1 %EDIR%\dekker-live2

src\erigone -a -t %1 %EDIR%\fair1
src\erigone -f -t %1 %EDIR%\fair1
src\erigone -a -t %1 %EDIR%\fair2
src\erigone -f -t %1 %EDIR%\fair2
src\erigone -f -t %1 %EDIR%\fair3
src\erigone -f -t %1 %EDIR%\fair4

src\erigone -r    %1 %EDIR%\ch-fifo
src\erigone -r    %1 %EDIR%\ch-sorted
src\erigone -r    %1 %EDIR%\ch-match
src\erigone -r    %1 %EDIR%\ch-random
src\erigone -r    %1 %EDIR%\ch-poll
src\erigone -r    %1 %EDIR%\ch-expr
src\erigone -r    %1 %EDIR%\ch-array
src\erigone -r    %1 %EDIR%\ch-array1

src\erigone -r    %1 %EDIR%\mtype
src\erigone -r    %1 %EDIR%\mtype1
src\erigone -r    %1 %EDIR%\anon

src\erigone -r    %1 %EDIR%\end
src\erigone -r    %1 %EDIR%\nrpr
src\erigone -r    %1 %EDIR%\pid
src\erigone -r    %1 %EDIR%\proctest
src\erigone -r    %1 %EDIR%\run

src\erigone -s    %1 %EDIR%\peterson1
src\erigone -t -a %1 %EDIR%\peterson2
src\erigone -t -f %1 %EDIR%\peterson2
src\erigone -t -a %1 %EDIR%\peterson3
src\erigone -t -f %1 %EDIR%\peterson3
src\erigone -t -a %1 %EDIR%\stepper
src\erigone -t -f %1 %EDIR%\stepper
