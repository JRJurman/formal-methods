	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* CLAIM Live */
;
		;
		
	case 4: /* STATE 5 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* CLAIM Safe */
;
		;
		
	case 6: /* STATE 8 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC :init: */

	case 7: /* STATE 1 */
		;
		((P2 *)this)->_6_i = trpt->bup.oval;
		;
		goto R999;

	case 8: /* STATE 2 */
		;
		(((int)((P2 *)this)->_6_i)<=2);
		;
		goto R999;

	case 9: /* STATE 4 */
		;
		((P2 *)this)->_6_i = trpt->bup.oval;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 10: /* STATE 10 */
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 11: /* STATE 12 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Elf */
;
		;
		
	case 13: /* STATE 2 */
		;
		_m = unsend(now.to_santa);
		;
		goto R999;

	case 14: /* STATE 3 */
		;
		XX = 1;
		unrecv(now.to_elf[ Index(((int)((P1 *)this)->id), 3) ], XX-1, 0, ((P1 *)this)->_5_toy_to_make, 1);
		((P1 *)this)->_5_toy_to_make = trpt->bup.oval;
		;
		;
		goto R999;

	case 15: /* STATE 4 */
		;
	/* 0 */	((P1 *)this)->_5_toy_to_make = trpt->bup.oval;
		;
		;
		goto R999;
;
		
	case 16: /* STATE 17 */
		goto R999;

	case 17: /* STATE 15 */
		;
		((P1 *)this)->_5_toys_made = trpt->bup.ovals[1];
		now.dolls = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 18: /* STATE 15 */
		;
		((P1 *)this)->_5_toys_made = trpt->bup.ovals[1];
		now.trains = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 19: /* STATE 15 */
		;
		((P1 *)this)->_5_toys_made = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 21: /* STATE 24 */
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Santa */
;
		;
		
	case 23: /* STATE 2 */
		;
	/* 0 */	((P0 *)this)->_4_nstops = trpt->bup.oval;
		;
		;
		goto R999;

	case 24: /* STATE 4 */
		;
		XX = 1;
		unrecv(now.to_santa, XX-1, 0, ((int)((P0 *)this)->_4_elf), 1);
		((P0 *)this)->_4_elf = trpt->bup.oval;
		;
		;
		goto R999;
;
		;
		
	case 26: /* STATE 6 */
		;
		_m = unsend(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]);
		;
		goto R999;

	case 27: /* STATE 7 */
		;
		((P0 *)this)->_4_nstops = trpt->bup.oval;
		;
		goto R999;

	case 28: /* STATE 17 */
		;
		((P0 *)this)->_4_total_assigned = trpt->bup.ovals[1];
		((P0 *)this)->_4_next_toy = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 29: /* STATE 17 */
		;
		((P0 *)this)->_4_total_assigned = trpt->bup.oval;
		;
		goto R999;

	case 30: /* STATE 17 */
		;
		((P0 *)this)->_4_total_assigned = trpt->bup.ovals[1];
		((P0 *)this)->_4_next_toy = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 31: /* STATE 18 */
		;
		_m = unsend(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]);
		;
		goto R999;
;
		;
		;
		;
		;
		;
		
	case 35: /* STATE 30 */
		;
		p_restor(II);
		;
		;
		goto R999;
	}

