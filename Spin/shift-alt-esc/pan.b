	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* CLAIM Liveness2 */
;
		;
		;
		;
		
	case 5: /* STATE 11 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* CLAIM Liveness */
;
		;
		;
		;
		
	case 8: /* STATE 11 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* CLAIM Safety2 */
;
		;
		
	case 10: /* STATE 6 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* CLAIM Safety */
;
		;
		;
		;
		;
		;
		
	case 14: /* STATE 20 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC :init: */

	case 15: /* STATE 1 */
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 16: /* STATE 2 */
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 17: /* STATE 3 */
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 18: /* STATE 4 */
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 19: /* STATE 5 */
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 20: /* STATE 7 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Server */
;
		;
		
	case 22: /* STATE 3 */
		;
		now.server_ready = trpt->bup.oval;
		;
		goto R999;

	case 23: /* STATE 6 */
		;
		((P2 *)this)->_5_cID = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 26: /* STATE 9 */
		;
		now.server_got[ Index(((P2 *)this)->_5_cID, 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 27: /* STATE 10 */
		;
		now.server_busy = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 29: /* STATE 12 */
		;
		now.orders[ Index(((P2 *)this)->_5_cID, 3) ].is_cooked = trpt->bup.oval;
		;
		goto R999;

	case 30: /* STATE 17 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Cashier */

	case 31: /* STATE 1 */
		;
		now.cashier_ready = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 33: /* STATE 5 */
		;
		now.customer_waiting = trpt->bup.oval;
		;
		goto R999;

	case 34: /* STATE 8 */
		;
		((P1 *)this)->_4_cID = trpt->bup.oval;
		;
		goto R999;

	case 35: /* STATE 9 */
		;
		now.orders[ Index(((P1 *)this)->_4_cID, 3) ].is_ready = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 37: /* STATE 13 */
		;
		now.orders[ Index(((P1 *)this)->_4_cID, 3) ].is_ordered = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 39: /* STATE 17 */
		;
		now.ready_order = trpt->bup.oval;
		;
		goto R999;

	case 40: /* STATE 18 */
		;
		now.server_ready = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 42: /* STATE 24 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Customer */
;
		;
		
	case 44: /* STATE 2 */
		;
		now.ready_customer = trpt->bup.oval;
		;
		goto R999;

	case 45: /* STATE 3 */
		;
		now.customer_waiting = trpt->bup.oval;
		;
		goto R999;

	case 46: /* STATE 6 */
		;
		now.orders[ Index(((P0 *)this)->id, 3) ].is_ready = trpt->bup.oval;
		;
		goto R999;

	case 47: /* STATE 10 */
		;
		now.cashier_ready = trpt->bup.oval;
		;
		goto R999;

	case 48: /* STATE 13 */
		;
		now.orders[ Index(((P0 *)this)->id, 3) ].customer = trpt->bup.oval;
		;
		goto R999;

	case 49: /* STATE 14 */
		;
		now.orders[ Index(((P0 *)this)->id, 3) ].food = trpt->bup.oval;
		;
		goto R999;

	case 50: /* STATE 15 */
		;
		now.orders[ Index(((P0 *)this)->id, 3) ].is_ordered = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 52: /* STATE 19 */
		;
		now.orders[ Index(((P0 *)this)->id, 3) ].is_cooked = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 54: /* STATE 26 */
		;
		p_restor(II);
		;
		;
		goto R999;
	}

