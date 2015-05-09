byte lcm = 0 ;

proctype LCM( byte ox ; byte oy ) {
	int x = ox ;
	int y = oy ;

	do
	:: x > y -> y = y + oy ;
	:: x < y -> x = x + ox ;
	:: x == y -> break ;
	od ;

	lcm = x ;
	printf("LCM of %d and %d is %d\n", ox, oy, lcm) ;
}

init {
	run LCM(32, 7) ;
}
