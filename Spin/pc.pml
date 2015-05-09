/*
 * Cirular buffer to hold messages (process id and a rotating value up to MAX).
 */
#define MAX 4
#define BUFSIZE 4

#define message byte

message buffer[BUFSIZE] ;
byte head = 0 ;
byte tail = 0 ;

#define sema byte
#define down(s) { atomic{s > 0 ; s--} }
#define up(s)   { s++ }

sema fullslots = 0 ;
sema emptyslots = BUFSIZE ;

sema p_mutex = 1 ;
byte p_want  = 0 ;
byte p_cs    = 0 ;

sema c_mutex = 1 ;
byte c_want  = 0 ;
byte c_cs    = 0 ;

active [2] proctype Producer(byte id) {
	do
	::
		/*
		 * Produce a message with a value
		 */
		printf("P%d produces an item\n", id) ;
    p_want++ ;
    down(p_mutex) ;

		/*
		 * Put message in next empty slot
		 */
		down(emptyslots) ;
    p_want-- ;

		buffer[tail] = id ;
		tail = (tail + 1) % BUFSIZE ;

		up(fullslots) ;
    up(p_mutex)
	od ;
}

active [2] proctype Consumer(byte id) {
	message from ;

	do
	::
		/*
		 * Get message from next full slot
		 */
    c_want++ ;
    down(c_mutex) ;
		down(fullslots) ;
    c_want-- ;

		from = buffer[head] ;
		head = (head + 1) % BUFSIZE ;

		up(emptyslots) ;
    up(c_mutex) ;

		printf("C%d consumes msg from P%d\n",
			id, from) ;
	od ;
}

init {
	atomic {
		run Producer(0) ;
		run Consumer(0) ;
		run Producer(1) ;
		run Consumer(1) ;
	}
}

ltl saftey_consumer {
  []( p_cs <= 1 )
}

ltl saftey_producer {
  []( p_cs <= 1 )
}

ltl live_producer {
  <>( p_want > 0 )
}

ltl live_consumer {
  <>( c_want > 0 )
}

ltl no_consumer_producer {
  [](!( (p_cs > 0) && (c_cs > 0) ) )
}
