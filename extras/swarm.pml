byte pos = 0;
byte val1 = 0;
byte val2 = 0;
byte val3 = 0;
byte flag1 = 1;
byte flag2 = 1;
byte flag3 = 1;
active proctype word()
{
do
:: pos < 8 -> flag1 = flag1 * 2; pos++
:: pos < 8 -> val1 = val1 + flag1; flag1 = flag1 * 2; pos++
:: pos >= 8 && pos < 16 -> flag2 = flag2 * 2; pos++
:: pos >= 8 && pos < 16 -> val2 = val2 + flag2; flag2 = flag2 * 2; pos++
:: pos >= 16 && pos < 18 -> flag3 = flag3 * 2; pos++
:: pos >= 16 && pos < 18 -> val3 = val3 + flag3; flag3 = flag3 * 2; pos++
:: else -> break
od;
printf("%d\n", val1);
printf("%d\n", val2);
printf("%d\n", val2);
assert((val1 != 255) || (val2 != 255) ||
 ((val1 == 255) && (val2 == 255) && (val3 == 7)));
}
