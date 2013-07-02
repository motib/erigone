#define board 8
#define diagonals 15
byte result[board];
bool a[board];
bool b[diagonals];
bool c[diagonals];

inline Write(n) {
  byte i;
  for (i : 1..n) {
    printf("%d, ", result[i-1])
  }
  printf("\n")
}

active proctype Queens() {
  byte col = 1;
  byte row;
  do
  ::  select(row : 1..board);
enda:  !a[row-1];
endb:  !b[row+col-2];
endc:  !c[row-col+7];
    a[row-1]     = true;
    b[row+col-2] = true;
    c[row-col+7] = true;
    result[col-1] = row;
    if
    :: col == board -> break
    :: else     -> col++
    fi
  od;
  _ = result[0];
  Write(board);
  Write(board);
  assert(false)
}
