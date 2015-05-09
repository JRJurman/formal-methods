#define rand	pan_rand
#if defined(HAS_CODE) && defined(VERBOSE)
	cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* CLAIM Liveness2 */
	case 3: /* STATE 1 - _spin_nvr.tmp:42 - [(!(server_busy))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported1 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported1)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported1 = 0;
			if (verbose && !reported1)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[7][1] = 1;
		if (!( !(((int)now.server_busy))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 4: /* STATE 7 - _spin_nvr.tmp:47 - [(!(server_busy))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported7 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported7)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported7 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported7 = 0;
			if (verbose && !reported7)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported7 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[7][7] = 1;
		if (!( !(((int)now.server_busy))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 5: /* STATE 11 - _spin_nvr.tmp:49 - [-end-] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported11 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported11)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported11 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported11 = 0;
			if (verbose && !reported11)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported11 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[7][11] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* CLAIM Liveness */
	case 6: /* STATE 1 - _spin_nvr.tmp:31 - [((!(!(wants_order[0]))&&!(places_order[0])))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported1 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported1)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported1 = 0;
			if (verbose && !reported1)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[6][1] = 1;
		if (!(( !( !(((int)now.wants_order[0])))&& !(((int)now.places_order[0])))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 7: /* STATE 7 - _spin_nvr.tmp:36 - [(!(places_order[0]))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported7 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported7)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported7 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported7 = 0;
			if (verbose && !reported7)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported7 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[6][7] = 1;
		if (!( !(((int)now.places_order[0]))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 8: /* STATE 11 - _spin_nvr.tmp:38 - [-end-] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported11 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported11)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported11 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported11 = 0;
			if (verbose && !reported11)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported11 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[6][11] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* CLAIM Safety2 */
	case 9: /* STATE 1 - _spin_nvr.tmp:23 - [(!(1))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported1 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported1)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported1 = 0;
			if (verbose && !reported1)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[5][1] = 1;
		if (!( !(1)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 10: /* STATE 6 - _spin_nvr.tmp:27 - [-end-] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported6 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported6)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported6 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported6 = 0;
			if (verbose && !reported6)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported6 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[5][6] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* CLAIM Safety */
	case 11: /* STATE 1 - _spin_nvr.tmp:3 - [(!((orders[0].food==server_got[0])))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported1 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported1)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported1 = 0;
			if (verbose && !reported1)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[4][1] = 1;
		if (!( !((now.orders[0].food==now.server_got[0]))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 12: /* STATE 5 - _spin_nvr.tmp:5 - [((!((orders[1].food==server_got[1]))||!((orders[2].food==server_got[2]))))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported5 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported5)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported5 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported5 = 0;
			if (verbose && !reported5)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported5 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[4][5] = 1;
		if (!(( !((now.orders[1].food==now.server_got[1]))|| !((now.orders[2].food==now.server_got[2])))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 13: /* STATE 13 - _spin_nvr.tmp:13 - [(!((orders[0].food==server_got[0])))] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported13 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported13)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported13 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported13 = 0;
			if (verbose && !reported13)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported13 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[4][13] = 1;
		if (!( !((now.orders[0].food==now.server_got[0]))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 14: /* STATE 20 - _spin_nvr.tmp:18 - [-end-] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported20 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported20)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported20 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported20 = 0;
			if (verbose && !reported20)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported20 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[4][20] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC :init: */
	case 15: /* STATE 1 - shift-alt-esc2.pml:106 - [(run Server(0))] (0:0:0 - 1) */
		IfNotBlocked
		reached[3][1] = 1;
		if (!(addproc(2, 0, 0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 16: /* STATE 2 - shift-alt-esc2.pml:107 - [(run Cashier(0))] (0:0:0 - 1) */
		IfNotBlocked
		reached[3][2] = 1;
		if (!(addproc(1, 0, 0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 17: /* STATE 3 - shift-alt-esc2.pml:108 - [(run Customer(0,PIZZA))] (0:0:0 - 1) */
		IfNotBlocked
		reached[3][3] = 1;
		if (!(addproc(0, 0, 1)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 18: /* STATE 4 - shift-alt-esc2.pml:109 - [(run Customer(1,CHILI))] (0:0:0 - 1) */
		IfNotBlocked
		reached[3][4] = 1;
		if (!(addproc(0, 1, 3)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 19: /* STATE 5 - shift-alt-esc2.pml:110 - [(run Customer(2,SANDWICH))] (0:0:0 - 1) */
		IfNotBlocked
		reached[3][5] = 1;
		if (!(addproc(0, 2, 2)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 20: /* STATE 7 - shift-alt-esc2.pml:112 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[3][7] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Server */
	case 21: /* STATE 1 - shift-alt-esc2.pml:89 - [printf('SERV%d waiting for order\\n',id)] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][1] = 1;
		Printf("SERV%d waiting for order\n", ((int)((P2 *)this)->id));
		_m = 3; goto P999; /* 0 */
	case 22: /* STATE 2 - shift-alt-esc2.pml:90 - [((server_ready>0))] (6:0:1 - 1) */
		IfNotBlocked
		reached[2][2] = 1;
		if (!((((int)now.server_ready)>0)))
			continue;
		/* merge: server_ready = (server_ready-1)(0, 3, 6) */
		reached[2][3] = 1;
		(trpt+1)->bup.oval = ((int)now.server_ready);
		now.server_ready = (((int)now.server_ready)-1);
#ifdef VAR_RANGES
		logval("server_ready", ((int)now.server_ready));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 23: /* STATE 6 - shift-alt-esc2.pml:92 - [cID = ready_order] (0:0:1 - 1) */
		IfNotBlocked
		reached[2][6] = 1;
		(trpt+1)->bup.oval = ((int)((P2 *)this)->_5_cID);
		((P2 *)this)->_5_cID = ((int)now.ready_order);
#ifdef VAR_RANGES
		logval("Server:cID", ((int)((P2 *)this)->_5_cID));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 24: /* STATE 7 - shift-alt-esc2.pml:93 - [printf('SERV%d retrieved order %e from CUST%d\\n',id,orders[cID].food,cID)] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][7] = 1;
		Printf("SERV%d retrieved order %e from CUST%d\n", ((int)((P2 *)this)->id), now.orders[ Index(((int)((P2 *)this)->_5_cID), 3) ].food, ((int)((P2 *)this)->_5_cID));
		_m = 3; goto P999; /* 0 */
	case 25: /* STATE 8 - shift-alt-esc2.pml:95 - [printf('SERV%d cooked order %e from CUST%d\\n',id,orders[cID].food,cID)] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][8] = 1;
		Printf("SERV%d cooked order %e from CUST%d\n", ((int)((P2 *)this)->id), now.orders[ Index(((int)((P2 *)this)->_5_cID), 3) ].food, ((int)((P2 *)this)->_5_cID));
		_m = 3; goto P999; /* 0 */
	case 26: /* STATE 9 - shift-alt-esc2.pml:96 - [server_got[cID] = orders[cID].food] (0:0:1 - 1) */
		IfNotBlocked
		reached[2][9] = 1;
		(trpt+1)->bup.oval = now.server_got[ Index(((int)((P2 *)this)->_5_cID), 3) ];
		now.server_got[ Index(((P2 *)this)->_5_cID, 3) ] = now.orders[ Index(((int)((P2 *)this)->_5_cID), 3) ].food;
#ifdef VAR_RANGES
		logval("server_got[Server:cID]", now.server_got[ Index(((int)((P2 *)this)->_5_cID), 3) ]);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 27: /* STATE 10 - shift-alt-esc2.pml:97 - [server_busy = 1] (0:0:1 - 1) */
		IfNotBlocked
		reached[2][10] = 1;
		(trpt+1)->bup.oval = ((int)now.server_busy);
		now.server_busy = 1;
#ifdef VAR_RANGES
		logval("server_busy", ((int)now.server_busy));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 28: /* STATE 11 - shift-alt-esc2.pml:99 - [printf('SERV%d deliver order %e to CUST%d\\n',id,orders[cID].food,cID)] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][11] = 1;
		Printf("SERV%d deliver order %e to CUST%d\n", ((int)((P2 *)this)->id), now.orders[ Index(((int)((P2 *)this)->_5_cID), 3) ].food, ((int)((P2 *)this)->_5_cID));
		_m = 3; goto P999; /* 0 */
	case 29: /* STATE 12 - shift-alt-esc2.pml:100 - [orders[cID].is_cooked = (orders[cID].is_cooked+1)] (0:0:1 - 1) */
		IfNotBlocked
		reached[2][12] = 1;
		(trpt+1)->bup.oval = ((int)now.orders[ Index(((int)((P2 *)this)->_5_cID), 3) ].is_cooked);
		now.orders[ Index(((P2 *)this)->_5_cID, 3) ].is_cooked = (((int)now.orders[ Index(((int)((P2 *)this)->_5_cID), 3) ].is_cooked)+1);
#ifdef VAR_RANGES
		logval("orders[Server:cID].is_cooked", ((int)now.orders[ Index(((int)((P2 *)this)->_5_cID), 3) ].is_cooked));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 30: /* STATE 17 - shift-alt-esc2.pml:102 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][17] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Cashier */
	case 31: /* STATE 1 - shift-alt-esc2.pml:66 - [cashier_ready = (cashier_ready+1)] (0:0:1 - 1) */
		IfNotBlocked
		reached[1][1] = 1;
		(trpt+1)->bup.oval = ((int)now.cashier_ready);
		now.cashier_ready = (((int)now.cashier_ready)+1);
#ifdef VAR_RANGES
		logval("cashier_ready", ((int)now.cashier_ready));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 32: /* STATE 3 - shift-alt-esc2.pml:67 - [printf('CASH%d waiting for new customers\\n',id)] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][3] = 1;
		Printf("CASH%d waiting for new customers\n", ((int)((P1 *)this)->id));
		_m = 3; goto P999; /* 0 */
	case 33: /* STATE 4 - shift-alt-esc2.pml:68 - [((customer_waiting>0))] (8:0:1 - 1) */
		IfNotBlocked
		reached[1][4] = 1;
		if (!((((int)now.customer_waiting)>0)))
			continue;
		/* merge: customer_waiting = (customer_waiting-1)(0, 5, 8) */
		reached[1][5] = 1;
		(trpt+1)->bup.oval = ((int)now.customer_waiting);
		now.customer_waiting = (((int)now.customer_waiting)-1);
#ifdef VAR_RANGES
		logval("customer_waiting", ((int)now.customer_waiting));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 34: /* STATE 8 - shift-alt-esc2.pml:69 - [cID = ready_customer] (0:0:1 - 1) */
		IfNotBlocked
		reached[1][8] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)this)->_4_cID);
		((P1 *)this)->_4_cID = ((int)now.ready_customer);
#ifdef VAR_RANGES
		logval("Cashier:cID", ((int)((P1 *)this)->_4_cID));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 35: /* STATE 9 - shift-alt-esc2.pml:70 - [orders[cID].is_ready = (orders[cID].is_ready+1)] (0:0:1 - 1) */
		IfNotBlocked
		reached[1][9] = 1;
		(trpt+1)->bup.oval = ((int)now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].is_ready);
		now.orders[ Index(((P1 *)this)->_4_cID, 3) ].is_ready = (((int)now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].is_ready)+1);
#ifdef VAR_RANGES
		logval("orders[Cashier:cID].is_ready", ((int)now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].is_ready));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 36: /* STATE 11 - shift-alt-esc2.pml:72 - [printf('CASH%d asks for CUST%d order\\n',id,cID)] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][11] = 1;
		Printf("CASH%d asks for CUST%d order\n", ((int)((P1 *)this)->id), ((int)((P1 *)this)->_4_cID));
		_m = 3; goto P999; /* 0 */
	case 37: /* STATE 12 - shift-alt-esc2.pml:74 - [((orders[cID].is_ordered>0))] (16:0:1 - 1) */
		IfNotBlocked
		reached[1][12] = 1;
		if (!((((int)now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].is_ordered)>0)))
			continue;
		/* merge: orders[cID].is_ordered = (orders[cID].is_ordered-1)(0, 13, 16) */
		reached[1][13] = 1;
		(trpt+1)->bup.oval = ((int)now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].is_ordered);
		now.orders[ Index(((P1 *)this)->_4_cID, 3) ].is_ordered = (((int)now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].is_ordered)-1);
#ifdef VAR_RANGES
		logval("orders[Cashier:cID].is_ordered", ((int)now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].is_ordered));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 38: /* STATE 16 - shift-alt-esc2.pml:75 - [printf('CASH%d takes CUST%d order for %e\\n',id,cID,orders[cID].food)] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][16] = 1;
		Printf("CASH%d takes CUST%d order for %e\n", ((int)((P1 *)this)->id), ((int)((P1 *)this)->_4_cID), now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].food);
		_m = 3; goto P999; /* 0 */
	case 39: /* STATE 17 - shift-alt-esc2.pml:77 - [ready_order = cID] (0:0:1 - 1) */
		IfNotBlocked
		reached[1][17] = 1;
		(trpt+1)->bup.oval = ((int)now.ready_order);
		now.ready_order = ((int)((P1 *)this)->_4_cID);
#ifdef VAR_RANGES
		logval("ready_order", ((int)now.ready_order));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 40: /* STATE 18 - shift-alt-esc2.pml:78 - [server_ready = (server_ready+1)] (0:0:1 - 1) */
		IfNotBlocked
		reached[1][18] = 1;
		(trpt+1)->bup.oval = ((int)now.server_ready);
		now.server_ready = (((int)now.server_ready)+1);
#ifdef VAR_RANGES
		logval("server_ready", ((int)now.server_ready));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 41: /* STATE 20 - shift-alt-esc2.pml:79 - [printf('CASH%d passes CUST%d order for %e to SERVER\\n',id,cID,orders[cID].food)] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][20] = 1;
		Printf("CASH%d passes CUST%d order for %e to SERVER\n", ((int)((P1 *)this)->id), ((int)((P1 *)this)->_4_cID), now.orders[ Index(((int)((P1 *)this)->_4_cID), 3) ].food);
		_m = 3; goto P999; /* 0 */
	case 42: /* STATE 24 - shift-alt-esc2.pml:81 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][24] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Customer */
	case 43: /* STATE 1 - shift-alt-esc2.pml:41 - [printf('CUST%d enters store (favorite: %e)\\n',id,favorite)] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][1] = 1;
		Printf("CUST%d enters store (favorite: %e)\n", ((int)((P0 *)this)->id), ((P0 *)this)->favorite);
		_m = 3; goto P999; /* 0 */
	case 44: /* STATE 2 - shift-alt-esc2.pml:43 - [ready_customer = id] (0:0:1 - 1) */
		IfNotBlocked
		reached[0][2] = 1;
		(trpt+1)->bup.oval = ((int)now.ready_customer);
		now.ready_customer = ((int)((P0 *)this)->id);
#ifdef VAR_RANGES
		logval("ready_customer", ((int)now.ready_customer));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 45: /* STATE 3 - shift-alt-esc2.pml:44 - [customer_waiting = (customer_waiting+1)] (0:0:1 - 1) */
		IfNotBlocked
		reached[0][3] = 1;
		(trpt+1)->bup.oval = ((int)now.customer_waiting);
		now.customer_waiting = (((int)now.customer_waiting)+1);
#ifdef VAR_RANGES
		logval("customer_waiting", ((int)now.customer_waiting));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 46: /* STATE 5 - shift-alt-esc2.pml:45 - [((orders[id].is_ready>0))] (12:0:1 - 1) */
		IfNotBlocked
		reached[0][5] = 1;
		if (!((((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_ready)>0)))
			continue;
		/* merge: orders[id].is_ready = (orders[id].is_ready-1)(0, 6, 12) */
		reached[0][6] = 1;
		(trpt+1)->bup.oval = ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_ready);
		now.orders[ Index(((P0 *)this)->id, 3) ].is_ready = (((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_ready)-1);
#ifdef VAR_RANGES
		logval("orders[Customer:id].is_ready", ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_ready));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 47: /* STATE 9 - shift-alt-esc2.pml:47 - [((cashier_ready>0))] (13:0:1 - 1) */
		IfNotBlocked
		reached[0][9] = 1;
		if (!((((int)now.cashier_ready)>0)))
			continue;
		/* merge: cashier_ready = (cashier_ready-1)(0, 10, 13) */
		reached[0][10] = 1;
		(trpt+1)->bup.oval = ((int)now.cashier_ready);
		now.cashier_ready = (((int)now.cashier_ready)-1);
#ifdef VAR_RANGES
		logval("cashier_ready", ((int)now.cashier_ready));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 48: /* STATE 13 - shift-alt-esc2.pml:49 - [orders[id].customer = id] (0:0:1 - 1) */
		IfNotBlocked
		reached[0][13] = 1;
		(trpt+1)->bup.oval = ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].customer);
		now.orders[ Index(((P0 *)this)->id, 3) ].customer = ((int)((P0 *)this)->id);
#ifdef VAR_RANGES
		logval("orders[Customer:id].customer", ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].customer));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 49: /* STATE 14 - shift-alt-esc2.pml:50 - [orders[id].food = favorite] (0:0:1 - 1) */
		IfNotBlocked
		reached[0][14] = 1;
		(trpt+1)->bup.oval = now.orders[ Index(((int)((P0 *)this)->id), 3) ].food;
		now.orders[ Index(((P0 *)this)->id, 3) ].food = ((P0 *)this)->favorite;
#ifdef VAR_RANGES
		logval("orders[Customer:id].food", now.orders[ Index(((int)((P0 *)this)->id), 3) ].food);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 50: /* STATE 15 - shift-alt-esc2.pml:51 - [orders[id].is_ordered = (orders[id].is_ordered+1)] (0:0:1 - 1) */
		IfNotBlocked
		reached[0][15] = 1;
		(trpt+1)->bup.oval = ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_ordered);
		now.orders[ Index(((P0 *)this)->id, 3) ].is_ordered = (((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_ordered)+1);
#ifdef VAR_RANGES
		logval("orders[Customer:id].is_ordered", ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_ordered));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 51: /* STATE 17 - shift-alt-esc2.pml:52 - [printf('CUST%d places an order for %e\\n',id,favorite)] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][17] = 1;
		Printf("CUST%d places an order for %e\n", ((int)((P0 *)this)->id), ((P0 *)this)->favorite);
		_m = 3; goto P999; /* 0 */
	case 52: /* STATE 18 - shift-alt-esc2.pml:54 - [((orders[id].is_cooked>0))] (22:0:1 - 1) */
		IfNotBlocked
		reached[0][18] = 1;
		if (!((((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_cooked)>0)))
			continue;
		/* merge: orders[id].is_cooked = (orders[id].is_cooked-1)(0, 19, 22) */
		reached[0][19] = 1;
		(trpt+1)->bup.oval = ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_cooked);
		now.orders[ Index(((P0 *)this)->id, 3) ].is_cooked = (((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_cooked)-1);
#ifdef VAR_RANGES
		logval("orders[Customer:id].is_cooked", ((int)now.orders[ Index(((int)((P0 *)this)->id), 3) ].is_cooked));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 53: /* STATE 22 - shift-alt-esc2.pml:56 - [printf('CUST%d exists with %e\\n',id,orders[id].food)] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][22] = 1;
		Printf("CUST%d exists with %e\n", ((int)((P0 *)this)->id), now.orders[ Index(((int)((P0 *)this)->id), 3) ].food);
		_m = 3; goto P999; /* 0 */
	case 54: /* STATE 26 - shift-alt-esc2.pml:58 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][26] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

