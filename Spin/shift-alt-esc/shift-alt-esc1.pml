#define message byte

#define sema byte
#define down(s) { atomic{s > 0 ; s--} }
#define up(s) { s++ }


#define NCUST 1
#define NCASH 1
#define NSERV 1

typedef order {
  byte customer ;
  mtype food ;
  sema is_ordered = 0 ;
  sema is_cooked = 0 ;
} ;

order orders[NCUST] ;

sema customer_waiting = 0 ;
sema cashier_ready = 0 ;
sema server_ready = 0 ;
byte ready_customer ;
byte ready_order ;
bool wants_order = false ;
bool places_order = false ;

mtype server_got ;

mtype = { CHILI, SANDWICH, PIZZA }

proctype Customer(byte id; mtype favorite) {
  do
  ::
    /* 1. ENTER STORE * */
    printf("CUST%d enters store (favorite: %e)\n", id, favorite) ;
    /* 2. RECORD A NEW CUSTOMER */
    ready_customer = id ;
    up(customer_waiting) ;
    /* 3. WAIT FOR CASHIER */
    wants_order = true ;
    down(cashier_ready) ;
    /* 4. PLACE ORDER FOR FAVORITE FOOD * */
    orders[id].customer = id ;
    orders[id].food = favorite ;
    up(orders[id].is_ordered)
    printf("CUST%d places an order for %e\n", id, favorite) ;
    places_order = true ;
    /* 5. WAIT FOR ORDER TO BE FULFILLED */
    down(orders[id].is_cooked)
    /* 6. EXIST STORE WITH FOOD * */
    printf("CUST%d exists with %e\n", id, orders[id].food) ;
  od ; 
}

proctype Cashier(byte id) {
  order customer_order ;
  byte cID ;
  do
  ::
    /* 1. WAIT FOR NEW CUSTOMER * */
    up(cashier_ready) ;
    printf("CASH%d waiting for new customers\n", id) ;
    down(customer_waiting) ;
    cID = ready_customer ;
    /* 2. SELECT A WAITING CUSTOMER * */
    printf("CASH%d asks for CUST%d order\n", id, cID ) ;
    /* 3. TAKE A ORDER * */
    down(orders[cID].is_ordered) ;
    printf("CASH%d takes CUST%d order for %e\n", id, cID, orders[cID].food) ;
    /* 4. PASS ORDER TO SERVER * */
    ready_order = cID ;
    up(server_ready) ;
    printf("CASH%d passes CUST%d order for %e to SERVER\n", id, cID, orders[cID].food) ;
  od ; 
}

proctype Server(byte id) {
  order customer_order ;
  byte cID ;
  do
  ::
    /* 1. WAIT FOR AN ORDER * */
    printf("SERV%d waiting for order\n", id) ; 
    down(server_ready) ;
    /* 2. RETREIVE ORDER ( CUSTOMER & FOOD ) * */
    cID = ready_order ;
    printf("SERV%d retrieved order %e from CUST%d\n", id, orders[cID].food, cID) ;
    /* 3. MAKE THE ORDER * */
    printf("SERV%d cooked order %e from CUST%d\n", id, orders[cID].food, cID) ;
    /* 4. DELIVER ORDER TO ( CORRECT ) CUSTOMER * */
    server_got = orders[cID].food ;
    printf("SERV%d deliver order %e to CUST%d\n", id, orders[cID].food, cID) ; 
    up(orders[cID].is_cooked) ;
    up(server_ready) ;
  od ; 
}

init {
  atomic {
    run Server(0) ;
    run Cashier(0) ;
    run Customer(0, PIZZA) ;
  }
}

// 1. The server always gives the correct food to the customer.
ltl Safety {
  <>[]( orders[0].food == server_got ) ;
}

// 1. It is always the case that if the customer wants to place an order then eventually the customer does so.
ltl Liveness {
  []( wants_order -> <>places_order )
}
