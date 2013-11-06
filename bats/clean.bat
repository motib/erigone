rem d = docs, e = examples, p = programs
del/s *.*~

if "%1"=="d" (
cd docs
del *.dvi
del *.log
del *.aux
cd ..
)

if "%1"=="e" (
del/s *.out
del/s *.aut
del/s *.trl
del/s *.lst
del/s *.dbg
del/s *.trc
)

if "%1"=="p" (
del/s *.ali
del/s *.o
del/s b~*.ad*
del/q src\obj
)

pause
