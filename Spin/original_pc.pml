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

proctype Producer(byte id) {
	do
	::
		/*
		 * Produce a message with a value
		 */
		printf("P%d produces an item\n", id) ;

		/*
		 * Put message in next empty slot
		 */
		down(emptyslots) ;

		buffer[tail] = id ;
		tail = (tail + 1) % BUFSIZE ;

		up(fullslots) ;
	od ;
}

proctype Consumer(byte id) {
	message from ;

	do
	::
		/*
		 * Get message from next full slot
		 */
		down(fullslots) ;

		from = buffer[head] ;
		head = (head + 1) % BUFSIZE ;

		up(emptyslots) ;

		printf("C%d consumes msg from P%d\n",
			id, from) ;
	od ;
}

init {
	atomic {
		run Producer(0) ;
		run Consumer(0) ;
	}
}