rem Run VMC - visualization of model checking 
cd vmc-examples
c:\erigone\src\erigone %2 %3 %4 -dehlmprs %1 > %1.trc
c:\erigone\vmc\vmc %1 > %1.dbg
mkdir %1
move %1*.dot %1
cd %1
for %%F in (%1-*.dot) do c:\"program files"\graphviz\bin\dot -Tpng %%F > %%~nF.png
cd ..
cd ..
