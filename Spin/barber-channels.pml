/*
 * Number of customers, number of chairs in the waiting room,
 * and a flag value for "no one" in a chair.
 */
#define NCUST 4
#define NBARB 2
#define NCHAIR 1
#define NO_ONE 255

/*
 * Channels to the room from the customer and the barber.
 * Channels that transmit customer id's have an mtype (the request)
 * and a byte (the id, if any).
 * Other channels simply take a request.
 */
chan customer_to_room = [0] of { mtype, byte } ;
chan barber_to_room = [0] of { mtype } ;

chan to_barber[NBARB] = [0] of { mtype, byte } ;
chan to_customer[NCUST] = [0] of { mtype } ;

/*
 * Customer to waiting room.
 */
mtype = { ENTER } ;

/*
 * Customer to barber.
 */
mtype = { IN_CHAIR } ;

/*
 * Waiting room to customer
 */
mtype = { SIT, NO_ROOM } ;

/*
 * Barber to customer
 */
mtype = { HAVE_A_SEAT } ;

/*
 * Waiting room to barber.
 */
mtype = { NAP, NEXT_CUST } ;

/*
 * Barber to waiting room and customer.
 */
mtype = { DONE } ;

/*
 * Customers.
 * Enter the waiting room.
 *   If "no room" exit the waiting room and come later.
 *   If the barber says "have a seat," sit in chair and wait til done.
 *   If told to "sit", sit in waiting room. When told "have a seat,"
 *      sit in the chair and wait til done.
 */
proctype Customer(byte id) {
	do
	::
		customer_to_room ! ENTER(id) ;
		if
		:: to_customer[id] ? NO_ROOM ->         /* no room to sit */
			printf("C%d leaves - no chair\n", id) ;

		:: to_customer[id] ? HAVE_A_SEAT, 0 ->     /* barber ready immediately */
            printf("C%d sits in the barber B0's chair\n", id) ;
			to_barber[0] ! IN_CHAIR(id) ;

		:: to_customer[id] ? HAVE_A_SEAT, 1 ->     /* barber ready immediately */
            printf("C%d sits in the barber B1's chair\n", id) ;
			to_barber[1] ! IN_CHAIR(id) ;

			to_customer[id] ? DONE ;
			printf("C%d exits with haircut\n", id) ;

		:: to_customer[id] ? SIT ->             /* sit and wait for barber */
            printf("C%d sits in the waiting room\n", id) ;
			to_customer[id] ? HAVE_A_SEAT ;

            printf("C%d sits in the barber chair\n", id) ;
			to_barber[0] ! IN_CHAIR(id) ;

		:: to_customer[id] ? SIT ->             /* sit and wait for barber */
            printf("C%d sits in the waiting room\n", id) ;
			to_customer[id] ? HAVE_A_SEAT ;

            printf("C%d sits in the barber chair\n", id) ;
			to_barber[1] ! IN_CHAIR(id) ;

			to_customer[id] ? DONE ;
			printf("C%d exits with haircut\n", id) ;
		fi ;			
	od ;
}

proctype Barber(byte id) {
	byte next_id = NO_ONE ; /* id from NEXT_CUST */
	byte in_id = NO_ONE ;   /* id from IN_CHAIR */
  bool napping = false ;  /* is the barber napping? */

	do
	:: to_barber[id] ? NAP, _  ->               /* take a nap */
        assert( ! napping ) ;
		printf("Barber B%d naps zzzzz\n", id) ;
		
	:: to_barber[id] ? NEXT_CUST(next_id) ->    /* next customer to serve */
		printf("Barber B%d invites C%d to sit\n", id, next_id) ;
		to_customer[next_id] ! HAVE_A_SEAT(id) ;
		
	:: to_barber[id] ? IN_CHAIR(in_id) ->       /* customer sits in chair */
		assert( next_id == in_id ) ;
		printf("Barber B%d gives C%d a haircut\n", id, in_id) ;

		barber_to_room ! DONE ;
		to_customer[in_id] ! DONE ;
	od ;
}

proctype WaitingRoom() {
	byte eid = 0 ;              /* id of customer entering */
	byte in_bchair[NBARB] = NO_ONE ;   /* id of customer in barber chair */
	byte in_wrchair = NO_ONE ;  /* id of customer in waiting room chair */

	to_barber[0] ! NAP, 0 ;
	to_barber[1] ! NAP, 0 ;
	do
	:: customer_to_room ? ENTER(eid) ->     /* customer enters */
		if
		:: in_wrchair != NO_ONE ->
			to_customer[eid] ! NO_ROOM ;

		:: in_bchair[0] == NO_ONE ->
			to_barber[0] ! NEXT_CUST(eid) ;
			in_bchair[0] = eid ;

		:: in_bchair[1] == NO_ONE ->
			to_barber[1] ! NEXT_CUST(eid) ;
			in_bchair[1] = eid ;

		:: else ->
			to_customer[eid] ! SIT ;
			in_wrchair = eid ;
		fi ;
	:: barber_to_room ? DONE ->             /* barber done with customer */
		if
		:: in_wrchair != NO_ONE ->
			to_barber[0] ! NEXT_CUST(in_wrchair) ;
			in_bchair[0] = in_wrchair ;
			in_wrchair = NO_ONE ;

		:: in_wrchair != NO_ONE ->
			to_barber[1] ! NEXT_CUST(in_wrchair) ;
			in_bchair[1] = in_wrchair ;
			in_wrchair = NO_ONE ;

		:: in_wrchair == NO_ONE ->
			to_barber[0] ! NAP, 0 ;
			in_bchair[0] = NO_ONE ;

		:: in_wrchair == NO_ONE ->
			to_barber[1] ! NAP, 0 ;
			in_bchair[1] = NO_ONE ;
		fi ;
	od ;
}

init {
	byte i ;

	atomic {
		for(i : 1 .. NCUST) {
			run Customer(i-1) ;
		}
		run Barber(0) ;
		run Barber(1) ;
		run WaitingRoom() ;
	}
}
