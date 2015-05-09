
/*
 * Pseudo-type sema(phore) and its operations.
 */
#define sema byte
#define up(s) { s++ ; }
#define down(s) { atomic{ s > 0 ; s-- } }

/*
 * Mutual exclusion semaphore
 */
sema mutex = 1 ;

/*
 * Blocking semaphores
 */
sema next_customer = 0 ;
sema haircut_done = 0 ;
sema waiting = 0 ;

#define NOBODY	255

/*
 * Shared state
 */
byte nwaiting = 0 ;
bool napping = true ;
byte serving = NOBODY ;












/*
 * The barber
 */
proctype Barber() {
	do
	::
		down(next_customer) ;
		if
		:: napping ->
			napping = false ;
			printf("Barber wakes up\n") ;
		:: else ->
			skip ;
		fi

		printf("Barber cuts C%d's hair\n", serving) ;

		up(haircut_done) ;

		down(mutex) ;
		if
		:: nwaiting == 0 ->
			serving = NOBODY ;
			printf("Barber naps\n") ;
			napping = true ;
			up(mutex) ;
		:: else ->
			up(waiting) ;
		fi ;
	od ;
		
}