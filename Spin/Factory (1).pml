/*
 * Configuration constants.
 */
#define CAPACITY 4	/* conveyer capacity */

/*
 * The various entities that comprise the
 * model.
 */
mtype = {PARTA, PARTB, UNIT, PACKAGE} ;

/*
 * Communications channels (conveyer belts)
 */

chan MA_to_Assembler       = [CAPACITY] of {mtype} ;
chan MB_to_Assembler       = [CAPACITY] of {mtype} ;
chan Assembler_to_Shipping = [CAPACITY] of {mtype} ;

/*
 * Machine A
 */
active proctype MA() {
  do
  ::
    printf("MA ships part A to Assembler\n") ;
    MA_to_Assembler ! PARTA ;
  od ;
}

/*
 * Machine B
 */
active proctype MB() {
  do
  ::
    printf("MB ships part B to Assembler\n") ;
    MB_to_Assembler ! PARTB ;
  od ;
}

/*
 * Assembler
 */
active proctype Assembler() {
	byte n_units = 0 ; /* number of units for current package */
  mtype partA ;
  mtype partB ;

  do
  :: 
    if
    :: n_units == 4 ->
      printf("Completed package ready for shipping\n") ;
      Assembler_to_Shipping ! PACKAGE ;
      n_units = 0 ;

    :: else -> 
      if
      :: MA_to_Assembler ? partA ->
        atomic {
          printf("Assembler recieves part A\n") ;
          MB_to_Assembler ? partB ->
            printf("Assembler recieves part B\n") ;
            n_units = n_units + 1 ;
            printf("Assembly of next unit complete (%d / 4 units) \n", n_units) ;
        }
      :: MB_to_Assembler ? partB ->
        atomic {
          printf("Assembler recieves part B\n") ;
          MA_to_Assembler ? partB ->
            printf("Assembler recieves part A\n") ;
            n_units = n_units + 1 ;
            printf("Assembly of next unit complete (%d / 4 units) \n", n_units) ;
        }
      fi ;
    fi ;
  od ;
}

/*
 * Shipping
 */
active proctype Shipping() {
  mtype u ;
  do
  ::
    Assembler_to_Shipping ? u ->
      printf("Shipping recieves another package\n") ;
  od ;
}
