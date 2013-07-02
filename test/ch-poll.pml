chan ch1 = [4] of { byte, byte, byte };
byte a, b, c;

active proctype p() {
  ch1 !  1, 2, 3;
  ch1 !  4, 5, 6;
  ch1 !  7, 8, 9;
  ch1 !  10, 11, 12;

  ch1 ?  [1, b, c] -> printf("1 _ _\n");

  ch1 ?? [a, 8, c] -> printf("_ 8 _\n");
}
