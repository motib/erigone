chan ch = [3] of { byte };


active proctype Sort() {
  byte n;
  if :: n = 1 :: n = 2 :: n = 3 fi;
  ch !! n;
  if :: n = 1 :: n = 2 :: n = 3 fi;
  ch !! n;
  if :: n = 1 :: n = 2 :: n = 3 fi;
  ch !! n;
  ch ? n; printf("%d\n", n);
  ch ? n; printf("%d\n", n);
  ch ? n; printf("%d\n", n)
}
