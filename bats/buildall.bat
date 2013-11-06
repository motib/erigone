cd docs
pdflatex -quiet erigone-ug
pdflatex -quiet erigone-ug
pdflatex -quiet erigone-quick
pdflatex -quiet erigone-quick
pdflatex -quiet erigone-soft
pdflatex -quiet erigone-soft
pause
cd ..\src
gnatmake -f -O1 -gnatn -Perigone
gnatmake    -O1 -gnatn -Pcompiler
cd ..\trace
gnatmake -f -O1 -gnatn -Ptrace
cd ..\list
gnatmake -f -O1 -gnatn -Plist
cd ..\vmc
gnatmake -f -O1 -gnatn -Pvmc
cd ..
pause
