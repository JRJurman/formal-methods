byte x = 1;

active proctype decrement() {
  int oldx = x ;

  printf("Hello, world\n") ;
  printf("x = %d\n", x) ;

  x-- ;

  printf("x = %d\n", x) ;
  assert( x <= oldx ) ;
}
