#define NP 4
#define NPM1 3


#define rfork(phid) phid
#define lfork(phid) ((phid + 1) % NP )

#define rphil(phid) ((phid + (NP - 1)) % NP )
#define lphil(phid) ((phid + 1) % NP )

mtype = {GET, PUT, EAT} ; 

chan to_table = [NP] of { mtype, btye } ;
chan to_phil[NP]  = [0] of { mtype }

proctype Phil(byte id) {
  do
  ::
    printf("P%d thinking\n", id) ; /* thinking */

    printf("P%d wants to eat\n", id) ;
    to_table ! GET(id) ;
    to_phil[id] ? EAT ;
    printf("P%d eating\n", id) ;
    
    printf("P%d done eating\n", id) ;
    to_table ! PUT(id)
  od ;

}

proctype Table() {
  bool phil_waiting[NP] = false ;
  bool fork_inuse[NP] = false ; 

  byte phid = 0 ;
  byte rphid = 0 ;
  byte lphid = 0 ;

  do
  :: to_table ? GET(phid) ->
    if
    :: ! fork_inuse[rfork(phid)] && ! fork_inuse[lfork(phid)] -> 
        fork_inuse[rfork(phid)] = true ; fork_inuse[lfork(phid)] = true ;
        to_phil[phid] ! EAT ;
    :: else ->
        phil_waiting[phid] = true ;
    fi ;

  :: to_table ? PUT(phid) ->
    fork_inuse[rfork(phid)] = false ; fork_inuse[lfork(phid)] = false ;
    rphid = rphil(phid) ; lphid = lphil(phid) ;

    if
    :: phil_waiting[rphid] && ! fork_inuse[rfork(rphid)] && ! fork_inuse[rfork(lphid)] ->
        fork_inuse[rfork(rphid)] = true ; fork_inuse[rfork(phid)] = true ;
        phil_waiting[rphid] = false ;
        to_phil[rphid] ! EAT ;
    :: else -> skip ;
    fi ;

    if
    :: phil_waiting[lphid] && ! fork_inuse[rfork(lphid)] && ! fork_inuse[lfork(lphid)] ->
        fork_inuse[lfork(lphid)] = true ; fork_inuse[lfork(phid)] = true ;
        phil_waiting[lphid] = false ;
        to_phil[lphid] ! EAT ;
    :: else -> skip ;
    fi ;
  od ;
}

init {
  atomic {
    run Phil(0) ;
    run Phil(1) ;
    run Phil(2) ;
    run Phil(3) ;
  }
}
