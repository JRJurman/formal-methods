/*****
 ** BYZANTINE GENERALS OUTLINE
 **
 ** You need not add any LTL claims; you need only be able to run the model with
 ** the configuration shown created by init and show consensus emerges.
 **
 *****/

/*
 * The two possible choices.
 */
#define RETREAT 0
#define ATTACK  1

/*
 * NL = number of loyal generals.
 * NT = number of traitors.
 * NG = number of generals in total.
 * NGM1 = number of generals - 1 (capacity of a generals' channel)
 */
#define NL 3
#define NT 1
#define NG 4
#define NGM1 3

/*
 * Pass for which a message is sent.
 */
mtype {PASS1, PASS2} ;

/*
 * The information from a general consists of the id
 * of the general and the array of NG bytes
 * representing the recommendations.
 *    Pass 1 - only the recommendation at the general's
 *             index is meaningful (his recommendation).
 *    Pass 1 - all recommendations are meaningful:
 *             his recommendation + what he heard from
 *             the other generals in pass 1.
 */
typedef Info {
    byte id;      /* id of sending general */
    byte rec[NG]  /* general's recommendation vector */
}

/*
 * One mailbox channel per general (NG) holding (NGM1) the pass and
 * the specific pass-dependent information.
 */
chan message[NG] = [NGM1] of {
    mtype,   /* pass indicator */
	Info     /* recommendation info */
} ;

/*
 * Each Loyal general starts with its id and the recommendation
 * it will make.
 */
proctype Loyal(byte id; byte rec) {
    Info receive ;     /* received message */
    Info send ;        /* sent message */

	Info table[NG] ;   /* table of information from each general */
    byte summary[NG] ; /* summary of recommendations from the 2nd pass */
    byte decision ;    /* the final decision (0 = retreat, 1 = attack) */
	/* other local variables as appropriate */

    /******
     * ALGORITHM OUTLINE
     *
     * Feel free to insert printf's to trace what is happening in each
     * Loyalist at each step.
     ******/

	/*
     * PASS 1
     * Send my recommendation (in the 'id'th slot of Info rec field)
     * to all *other* generals.
     * Do atomically to cut down on the state space.
     */
    atomic {
      printf("L%d PASS 1, send-rec: %d\n", id, rec) ;

      send.id = id ;
      send.rec[id] = rec ;

      byte i ;
      for ( i : 0 .. NGM1 ) {
        if 
        :: ( i != id ) -> 
          message[i] ! PASS1(send) ;
        :: else ->
          skip ;
        fi ;
      }
    }

	/*
     * Get all the PASS1 recommendations from *other* generals and
     * construct my row (row 'id') in the Info table.
     * Do atomically to cut down on the state space.
     */
    atomic {
      byte i ;
      for ( i : 1 .. NGM1 ) {
        message[id] ? PASS1(receive) -> 
        printf("L%d PASS 1, from G%d - rec: %d\n", id, receive.id, receive.rec[receive.id]) ;
        if 
        :: ( i != id ) -> 
          table[id].id = receive.id ;
          table[id].rec[receive.id] = receive.rec[receive.id] ;
        :: else ->
          skip ;
        fi ;
      }
    }

    /*
     * PASS 2
     * Send my vector with my recommendation and what I heard from
     * the *other* generals to all the *other* generals.
     * Do atomically to cut down on the state space.
     */
    atomic {
      byte i ;
      for(i : 0 .. NGM1) {
        if
        :: i != id ->
          printf("L%d PASS 2, from G%d - rec: %d\n", id, i, table[id].rec[i]) ;
          message[i] ! PASS2(table[id]) ;
        :: else ->
          skip
        fi ;
      }
    }

	/*
     * Get all the PASS2 recommendations from *other* generals and
     * construct the *other* generals' rows in the Info table.
     * Do atomically to cut down on the state space.
     */
    atomic {
        skip ;
    }

    /*
     * Compute the majority selection for each column and store the
     * result in the summary array:
     *    * Just record my own recommendation in my slot directly (I
     *      don't care what others say I recommended).
     *    * For each general with identification 'id', ignore the
     *      'id'th column of the 'id'th row to prevent double voting.
     * Do atomically to cut down on the state space.
     */
    atomic {
        skip ;
    }

    /*
     * Use the summary array to determine the overall decision
     * (tie recommendations mean retreat).
     * Do atomically to cut down on the state space.
     */
    atomic {
        skip ;
    }

    /*
     * Print the decision.
     */
    atomic  {
    	printf("Loyal General %d says ", id) ;
        if
        :: decision == RETREAT -> printf("RETREAT\n") ;
        :: decision == ATTACK ->  printf("ATTACK\n") ;
        fi ;
    }
}

/*
 * Each Traitor starts with its id.
 */
proctype Traitor(byte id) {
    Info received ;      /* what we receive from each general */
    Info deception[NG] ; /* what we send each general to deceive him */

    byte pass1[NG] ;     /* the recommendation from each general on pass 1 */
	/* other local variables as appropriate */

    /******
     * ALGORITHM OUTLINE
     *
     * Feel free to insert printf's to trace what is happening in each
     * Traitor at each step.
     ******/

	/*
     * PASS 1
     * Get messages from each *other* general and send back to him
     * a "deception" message saying my decision is the same as
     * his. Record each general's recommendation in the pass1
     * array.
     * Do atomically to cut down on the state space.
     */
    atomic {
      printf("T%d PASS 1\n", id) ;

      byte i ;
      for ( i : 1 .. NGM1 ) {
        message[id] ? PASS1(received) -> 
          printf("T%d received L%d reccomendation: %d\n", id, received.id, received.rec[received.id]) ;
          deception[received.id].id = id  ;
          deception[received.id].rec[id] = received.rec[received.id] ;
          pass1[received.id] = received.rec[received.id] ;
          message[received.id] ! PASS1(deception[received.id]) ;
      }
    }

    /*
     * PASS 2
     * Send to each *other* general a "deception" message saying
     * everyone agrees with him.
     * That is, for every other general 'oid', fill in the
     * "deception" Info array with the contents of "pass1[oid]"
     * before sending.
     * Do atomically to cut down on the state space.
     */
    atomic {
      printf("T%d PASS 2\n", id) ;

      byte oid ;
      for ( oid : 1 .. NGM1 ) {
        printf("T%d sending to L%d reccomendation: %d\n", id, oid, pass1[oid]) ;
        //deception[oid].id = oid
        //deception[oid].rec[id] = pass1[oid]
        message[oid] ! PASS2(deception[oid])  
      }
    }
}

/*
 * This configuration mirrors the one in the powerpoint presentation.
 */
init {
  atomic {
    run Loyal(0, RETREAT) ;
    run Loyal(1, ATTACK) ;
    run Loyal(2, ATTACK) ;
    run Traitor(3)
  }
}





















