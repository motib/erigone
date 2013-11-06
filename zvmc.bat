cd vmc-examples
7z u -r -tzip vmc-examples-%1.zip *.pml *.prg *.png *.dot
copy vmc-examples-%1.zip \zip\
copy vmc-examples-%1.zip n:\zip\
move vmc-examples-%1.zip ..\dist\
cd ..
pause
