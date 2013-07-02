byte result[4];  
bool a[4];  
bool b[7];  
bool c[7];  

active proctype Queens (  )  {  
  byte col = 1;  
  byte row, i;
  do 
  :: row=1;  
     do
     :: row < 4 -> 
          row++ 
     :: break
     od;  
     enda: !a[row - 1];  
     endb: !b[row + col - 2];  
     endc: !c[row - col + 3];  
     a[row - 1] = true;  
     b[row + col - 2] = true;  
     c[row - col + 3] = true;  
     result[col - 1] = row;  
     if 
     :: col == 4 -> break 
     :: else     ->
          col++ 
     fi
  od;  
  i = 0;
  do
  :: i < 4 ->
       printf(" %d", result[i]);
       i++
  :: else  -> break
  od;
  printf("\n");
  assert(false)  
}  
