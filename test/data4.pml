byte a, b, c;

active proctype P() {
  /* Check conditional expressions */
  a = 3;
  b = 4;
  c = (a > b -> a+2 : b+3);
  printf("%d %d %d\n", a, b, c);
  c = (a < b -> a+2 : b+3);
  printf("%d %d %d\n", a, b, c);

  /* Check short-circuit logical operators */
  a = 3;
  b = 4;
  if
  :: (a >  3) && (b/0 == 4) ->
        printf("Shouldn't be here\n")
  :: (a == 3) && (b > 4)    ->
        printf("Shouldn't be here\n")
  :: (a == 3) && (b == 4)   ->
        printf("OK\n");
  fi;
  if
  :: (a >  3) || (b >  4)   ->
        printf("Shouldn't be here\n")
  :: (a == 3) || (b/0 == 4) ->
        printf("OK\n");
  fi;
  if
  :: (a >  3) || (b >  4)   ->
        printf("Shouldn't be here\n")
  :: (a >  3) || (b == 4) ->
        printf("OK\n");
  fi;

  /* Check bitwise operators */
  a = 129;
  b = 126;
  c = a | b;
  printf("%d %d %d\n", a, b, c);
  a = 15;
  b = 9;
  c = a & b;
  printf("%d %d %d\n", a, b, c);
  c = a ^ b;
  printf("%d %d %d\n", a, b, c);
  b = a << 3;
  c = a >> 2;
  printf("%d %d %d\n", a, b, c);
}
