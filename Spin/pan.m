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

		 /* CLAIM Live */
	case 3: /* STATE 1 - _spin_nvr.tmp:13 - [(!(((dolls+trains)==10)))] (0:0:0 - 1) */
		
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
		if (!( !(((((int)now.dolls)+((int)now.trains))==10))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 4: /* STATE 5 - _spin_nvr.tmp:15 - [-end-] (0:0:0 - 1) */
		
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
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* CLAIM Safe */
	case 5: /* STATE 1 - _spin_nvr.tmp:3 - [(!(((dolls+trains)<10)))] (0:0:0 - 1) */
		
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
		reached[3][1] = 1;
		if (!( !(((((int)now.dolls)+((int)now.trains))<10))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 6: /* STATE 8 - _spin_nvr.tmp:8 - [-end-] (0:0:0 - 1) */
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported8 = 0; int nn = (int) ((Pclaim *)this)->_n;
			if (verbose && !reported8)
			{	printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported8 = 1;
				fflush(stdout);
		}	}
#else
{	static int reported8 = 0;
			if (verbose && !reported8)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)this)->_p, src_claim[ (int) ((Pclaim *)this)->_p ]);
				reported8 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[3][8] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC :init: */
	case 7: /* STATE 1 - santa.pml:172 - [i = 0] (0:0:1 - 1) */
		IfNotBlocked
		reached[2][1] = 1;
		(trpt+1)->bup.oval = ((int)((P2 *)this)->_6_i);
		((P2 *)this)->_6_i = 0;
#ifdef VAR_RANGES
		logval(":init::i", ((int)((P2 *)this)->_6_i));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 8: /* STATE 2 - santa.pml:172 - [(i<=2)] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][2] = 1;
		(((int)((P2 *)this)->_6_i)<=2);
		_m = 3; goto P999; /* 0 */
	case 9: /* STATE 3 - santa.pml:173 - [(run Elf(i))] (7:0:1 - 1) */
		IfNotBlocked
		reached[2][3] = 1;
		if (!(addproc(1, ((int)((P2 *)this)->_6_i))))
			continue;
		/* merge: i = (i+1)(0, 4, 7) */
		reached[2][4] = 1;
		(trpt+1)->bup.oval = ((int)((P2 *)this)->_6_i);
		((P2 *)this)->_6_i = (((int)((P2 *)this)->_6_i)+1);
#ifdef VAR_RANGES
		logval(":init::i", ((int)((P2 *)this)->_6_i));
#endif
		;
		/* merge: .(goto)(0, 8, 7) */
		reached[2][8] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 10: /* STATE 10 - santa.pml:175 - [(run Santa())] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][10] = 1;
		if (!(addproc(0, 0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 11: /* STATE 12 - santa.pml:177 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[2][12] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Elf */
	case 12: /* STATE 1 - santa.pml:129 - [printf('Elf %d arrives at work\\n',id)] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][1] = 1;
		Printf("Elf %d arrives at work\n", ((int)((P1 *)this)->id));
		_m = 3; goto P999; /* 0 */
	case 13: /* STATE 2 - santa.pml:134 - [to_santa!id] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][2] = 1;
		if (q_full(now.to_santa))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[32];
			sprintf(simvals, "%d!", now.to_santa);
		sprintf(simtmp, "%d", ((int)((P1 *)this)->id)); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.to_santa, 0, ((int)((P1 *)this)->id), 1);
		if (q_zero(now.to_santa)) { boq = now.to_santa; };
		_m = 2; goto P999; /* 0 */
	case 14: /* STATE 3 - santa.pml:135 - [to_elf[id]?toy_to_make] (0:0:1 - 1) */
		reached[1][3] = 1;
		if (q_zero(now.to_elf[ Index(((int)((P1 *)this)->id), 3) ]))
		{	if (boq != now.to_elf[ Index(((int)((P1 *)this)->id), 3) ]) continue;
		} else
		{	if (boq != -1) continue;
		}
		if (q_len(now.to_elf[ Index(((int)((P1 *)this)->id), 3) ]) == 0) continue;

		XX=1;
		(trpt+1)->bup.oval = ((P1 *)this)->_5_toy_to_make;
		;
		((P1 *)this)->_5_toy_to_make = qrecv(now.to_elf[ Index(((int)((P1 *)this)->id), 3) ], XX-1, 0, 1);
#ifdef VAR_RANGES
		logval("Elf:toy_to_make", ((P1 *)this)->_5_toy_to_make);
#endif
		;
		
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[32];
			sprintf(simvals, "%d?", now.to_elf[ Index(((int)((P1 *)this)->id), 3) ]);
		sprintf(simtmp, "%d", ((P1 *)this)->_5_toy_to_make); strcat(simvals, simtmp);		}
#endif
		if (q_zero(now.to_elf[ Index(((int)((P1 *)this)->id), 3) ]))
		{	boq = -1;
#ifndef NOFAIR
			if (fairness
			&& !(trpt->o_pm&32)
			&& (now._a_t&2)
			&&  now._cnt[now._a_t&1] == II+2)
			{	now._cnt[now._a_t&1] -= 1;
#ifdef VERI
				if (II == 1)
					now._cnt[now._a_t&1] = 1;
#endif
#ifdef DEBUG
			printf("%3d: proc %d fairness ", depth, II);
			printf("Rule 2: --cnt to %d (%d)\n",
				now._cnt[now._a_t&1], now._a_t);
#endif
				trpt->o_pm |= (32|64);
			}
#endif

		};
		_m = 4; goto P999; /* 0 */
	case 15: /* STATE 4 - santa.pml:137 - [((toy_to_make==STOP))] (22:0:1 - 1) */
		IfNotBlocked
		reached[1][4] = 1;
		if (!((((P1 *)this)->_5_toy_to_make==1)))
			continue;
		/* dead 1: _5_toy_to_make */  (trpt+1)->bup.oval = ((P1 *)this)->_5_toy_to_make;
#ifdef HAS_CODE
		if (!readtrail)
#endif
			((P1 *)this)->_5_toy_to_make = 0;
		/* merge: goto :b1(0, 5, 22) */
		reached[1][5] = 1;
		;
		_m = 3; goto P999; /* 1 */
	case 16: /* STATE 17 - santa.pml:152 - [.(goto)] (0:20:0 - 1) */
		IfNotBlocked
		reached[1][17] = 1;
		;
		/* merge: printf('Elf %d made a %e for a total of %d toys\\n',id,toy_to_make,toys_made)(20, 19, 20) */
		reached[1][19] = 1;
		Printf("Elf %d made a %e for a total of %d toys\n", ((int)((P1 *)this)->id), ((P1 *)this)->_5_toy_to_make, ((int)((P1 *)this)->_5_toys_made));
		/* merge: .(goto)(0, 21, 20) */
		reached[1][21] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 17: /* STATE 7 - santa.pml:141 - [((toy_to_make==DOLL))] (20:0:2 - 1) */
		IfNotBlocked
		reached[1][7] = 1;
		if (!((((P1 *)this)->_5_toy_to_make==3)))
			continue;
		/* merge: printf('Elf %d created a new DOLL (total toys : %d)\\n',id,toys_made)(20, 8, 20) */
		reached[1][8] = 1;
		Printf("Elf %d created a new DOLL (total toys : %d)\n", ((int)((P1 *)this)->id), ((int)((P1 *)this)->_5_toys_made));
		/* merge: dolls = (dolls+1)(20, 9, 20) */
		reached[1][9] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = ((int)now.dolls);
		now.dolls = (((int)now.dolls)+1);
#ifdef VAR_RANGES
		logval("dolls", ((int)now.dolls));
#endif
		;
		/* merge: .(goto)(20, 14, 20) */
		reached[1][14] = 1;
		;
		/* merge: toys_made = (toys_made+1)(20, 15, 20) */
		reached[1][15] = 1;
		(trpt+1)->bup.ovals[1] = ((int)((P1 *)this)->_5_toys_made);
		((P1 *)this)->_5_toys_made = (((int)((P1 *)this)->_5_toys_made)+1);
#ifdef VAR_RANGES
		logval("Elf:toys_made", ((int)((P1 *)this)->_5_toys_made));
#endif
		;
		/* merge: .(goto)(20, 17, 20) */
		reached[1][17] = 1;
		;
		/* merge: printf('Elf %d made a %e for a total of %d toys\\n',id,toy_to_make,toys_made)(20, 19, 20) */
		reached[1][19] = 1;
		Printf("Elf %d made a %e for a total of %d toys\n", ((int)((P1 *)this)->id), ((P1 *)this)->_5_toy_to_make, ((int)((P1 *)this)->_5_toys_made));
		/* merge: .(goto)(0, 21, 20) */
		reached[1][21] = 1;
		;
		_m = 3; goto P999; /* 7 */
	case 18: /* STATE 10 - santa.pml:144 - [((toy_to_make==TRAIN))] (20:0:2 - 1) */
		IfNotBlocked
		reached[1][10] = 1;
		if (!((((P1 *)this)->_5_toy_to_make==2)))
			continue;
		/* merge: printf('Elf %d created a new TRAIN (total toys : %d)\\n',id,toys_made)(20, 11, 20) */
		reached[1][11] = 1;
		Printf("Elf %d created a new TRAIN (total toys : %d)\n", ((int)((P1 *)this)->id), ((int)((P1 *)this)->_5_toys_made));
		/* merge: trains = (trains+1)(20, 12, 20) */
		reached[1][12] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = ((int)now.trains);
		now.trains = (((int)now.trains)+1);
#ifdef VAR_RANGES
		logval("trains", ((int)now.trains));
#endif
		;
		/* merge: .(goto)(20, 14, 20) */
		reached[1][14] = 1;
		;
		/* merge: toys_made = (toys_made+1)(20, 15, 20) */
		reached[1][15] = 1;
		(trpt+1)->bup.ovals[1] = ((int)((P1 *)this)->_5_toys_made);
		((P1 *)this)->_5_toys_made = (((int)((P1 *)this)->_5_toys_made)+1);
#ifdef VAR_RANGES
		logval("Elf:toys_made", ((int)((P1 *)this)->_5_toys_made));
#endif
		;
		/* merge: .(goto)(20, 17, 20) */
		reached[1][17] = 1;
		;
		/* merge: printf('Elf %d made a %e for a total of %d toys\\n',id,toy_to_make,toys_made)(20, 19, 20) */
		reached[1][19] = 1;
		Printf("Elf %d made a %e for a total of %d toys\n", ((int)((P1 *)this)->id), ((P1 *)this)->_5_toy_to_make, ((int)((P1 *)this)->_5_toys_made));
		/* merge: .(goto)(0, 21, 20) */
		reached[1][21] = 1;
		;
		_m = 3; goto P999; /* 7 */
	case 19: /* STATE 15 - santa.pml:148 - [toys_made = (toys_made+1)] (0:20:1 - 3) */
		IfNotBlocked
		reached[1][15] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)this)->_5_toys_made);
		((P1 *)this)->_5_toys_made = (((int)((P1 *)this)->_5_toys_made)+1);
#ifdef VAR_RANGES
		logval("Elf:toys_made", ((int)((P1 *)this)->_5_toys_made));
#endif
		;
		/* merge: .(goto)(20, 17, 20) */
		reached[1][17] = 1;
		;
		/* merge: printf('Elf %d made a %e for a total of %d toys\\n',id,toy_to_make,toys_made)(20, 19, 20) */
		reached[1][19] = 1;
		Printf("Elf %d made a %e for a total of %d toys\n", ((int)((P1 *)this)->id), ((P1 *)this)->_5_toy_to_make, ((int)((P1 *)this)->_5_toys_made));
		/* merge: .(goto)(0, 21, 20) */
		reached[1][21] = 1;
		;
		_m = 3; goto P999; /* 3 */
	case 20: /* STATE 23 - santa.pml:162 - [printf('Elf %d leaves after making %d toys\\n',id,toys_made)] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][23] = 1;
		Printf("Elf %d leaves after making %d toys\n", ((int)((P1 *)this)->id), ((int)((P1 *)this)->_5_toys_made));
		_m = 3; goto P999; /* 0 */
	case 21: /* STATE 24 - santa.pml:163 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[1][24] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Santa */
	case 22: /* STATE 1 - santa.pml:77 - [printf('Santa arrives at work\\n')] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][1] = 1;
		Printf("Santa arrives at work\n");
		_m = 3; goto P999; /* 0 */
	case 23: /* STATE 2 - santa.pml:82 - [((nstops==3))] (0:0:1 - 1) */
		IfNotBlocked
		reached[0][2] = 1;
		if (!((((int)((P0 *)this)->_4_nstops)==3)))
			continue;
		/* dead 1: _4_nstops */  (trpt+1)->bup.oval = ((P0 *)this)->_4_nstops;
#ifdef HAS_CODE
		if (!readtrail)
#endif
			((P0 *)this)->_4_nstops = 0;
		_m = 3; goto P999; /* 0 */
	case 24: /* STATE 4 - santa.pml:84 - [to_santa?elf] (0:0:1 - 1) */
		reached[0][4] = 1;
		if (q_zero(now.to_santa))
		{	if (boq != now.to_santa) continue;
		} else
		{	if (boq != -1) continue;
		}
		if (q_len(now.to_santa) == 0) continue;

		XX=1;
		(trpt+1)->bup.oval = ((int)((P0 *)this)->_4_elf);
		;
		((P0 *)this)->_4_elf = qrecv(now.to_santa, XX-1, 0, 1);
#ifdef VAR_RANGES
		logval("Santa:elf", ((int)((P0 *)this)->_4_elf));
#endif
		;
		
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[32];
			sprintf(simvals, "%d?", now.to_santa);
		sprintf(simtmp, "%d", ((int)((P0 *)this)->_4_elf)); strcat(simvals, simtmp);		}
#endif
		if (q_zero(now.to_santa))
		{	boq = -1;
#ifndef NOFAIR
			if (fairness
			&& !(trpt->o_pm&32)
			&& (now._a_t&2)
			&&  now._cnt[now._a_t&1] == II+2)
			{	now._cnt[now._a_t&1] -= 1;
#ifdef VERI
				if (II == 1)
					now._cnt[now._a_t&1] = 1;
#endif
#ifdef DEBUG
			printf("%3d: proc %d fairness ", depth, II);
			printf("Rule 2: --cnt to %d (%d)\n",
				now._cnt[now._a_t&1], now._a_t);
#endif
				trpt->o_pm |= (32|64);
			}
#endif

		};
		_m = 4; goto P999; /* 0 */
	case 25: /* STATE 5 - santa.pml:86 - [((total_assigned==10))] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][5] = 1;
		if (!((((int)((P0 *)this)->_4_total_assigned)==10)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 26: /* STATE 6 - santa.pml:87 - [to_elf[elf]!STOP] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][6] = 1;
		if (q_full(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[32];
			sprintf(simvals, "%d!", now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]);
		sprintf(simtmp, "%d", 1); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ], 0, 1, 1);
		if (q_zero(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ])) { boq = now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]; };
		_m = 2; goto P999; /* 0 */
	case 27: /* STATE 7 - santa.pml:88 - [nstops = (nstops+1)] (0:0:1 - 1) */
		IfNotBlocked
		reached[0][7] = 1;
		(trpt+1)->bup.oval = ((int)((P0 *)this)->_4_nstops);
		((P0 *)this)->_4_nstops = (((int)((P0 *)this)->_4_nstops)+1);
#ifdef VAR_RANGES
		logval("Santa:nstops", ((int)((P0 *)this)->_4_nstops));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 28: /* STATE 9 - santa.pml:19 - [(1)] (18:0:2 - 1) */
		IfNotBlocked
		reached[0][9] = 1;
		if (!(1))
			continue;
		/* merge: next_toy = DOLL(18, 10, 18) */
		reached[0][10] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = ((P0 *)this)->_4_next_toy;
		((P0 *)this)->_4_next_toy = 3;
#ifdef VAR_RANGES
		logval("Santa:next_toy", ((P0 *)this)->_4_next_toy);
#endif
		;
		/* merge: .(goto)(18, 14, 18) */
		reached[0][14] = 1;
		;
		/* merge: total_assigned = (total_assigned+1)(18, 17, 18) */
		reached[0][17] = 1;
		(trpt+1)->bup.ovals[1] = ((int)((P0 *)this)->_4_total_assigned);
		((P0 *)this)->_4_total_assigned = (((int)((P0 *)this)->_4_total_assigned)+1);
#ifdef VAR_RANGES
		logval("Santa:total_assigned", ((int)((P0 *)this)->_4_total_assigned));
#endif
		;
		_m = 3; goto P999; /* 3 */
	case 29: /* STATE 14 - santa.pml:22 - [.(goto)] (0:18:1 - 2) */
		IfNotBlocked
		reached[0][14] = 1;
		;
		/* merge: total_assigned = (total_assigned+1)(18, 17, 18) */
		reached[0][17] = 1;
		(trpt+1)->bup.oval = ((int)((P0 *)this)->_4_total_assigned);
		((P0 *)this)->_4_total_assigned = (((int)((P0 *)this)->_4_total_assigned)+1);
#ifdef VAR_RANGES
		logval("Santa:total_assigned", ((int)((P0 *)this)->_4_total_assigned));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 30: /* STATE 11 - santa.pml:20 - [(1)] (18:0:2 - 1) */
		IfNotBlocked
		reached[0][11] = 1;
		if (!(1))
			continue;
		/* merge: next_toy = TRAIN(18, 12, 18) */
		reached[0][12] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = ((P0 *)this)->_4_next_toy;
		((P0 *)this)->_4_next_toy = 2;
#ifdef VAR_RANGES
		logval("Santa:next_toy", ((P0 *)this)->_4_next_toy);
#endif
		;
		/* merge: .(goto)(18, 14, 18) */
		reached[0][14] = 1;
		;
		/* merge: total_assigned = (total_assigned+1)(18, 17, 18) */
		reached[0][17] = 1;
		(trpt+1)->bup.ovals[1] = ((int)((P0 *)this)->_4_total_assigned);
		((P0 *)this)->_4_total_assigned = (((int)((P0 *)this)->_4_total_assigned)+1);
#ifdef VAR_RANGES
		logval("Santa:total_assigned", ((int)((P0 *)this)->_4_total_assigned));
#endif
		;
		_m = 3; goto P999; /* 3 */
	case 31: /* STATE 18 - santa.pml:92 - [to_elf[elf]!next_toy] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][18] = 1;
		if (q_full(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]))
			continue;
#ifdef HAS_CODE
		if (readtrail && gui) {
			char simtmp[32];
			sprintf(simvals, "%d!", now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]);
		sprintf(simtmp, "%d", ((P0 *)this)->_4_next_toy); strcat(simvals, simtmp);		}
#endif
		
		qsend(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ], 0, ((P0 *)this)->_4_next_toy, 1);
		if (q_zero(now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ])) { boq = now.to_elf[ Index(((int)((P0 *)this)->_4_elf), 3) ]; };
		_m = 2; goto P999; /* 0 */
	case 32: /* STATE 22 - santa.pml:95 - [printf('Waiting for elves to message\\n')] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][22] = 1;
		Printf("Waiting for elves to message\n");
		_m = 3; goto P999; /* 0 */
	case 33: /* STATE 28 - santa.pml:99 - [printf('Quota %d, Dolls %d, Trains %d\\n',10,dolls,trains)] (0:0:0 - 3) */
		IfNotBlocked
		reached[0][28] = 1;
		Printf("Quota %d, Dolls %d, Trains %d\n", 10, ((int)now.dolls), ((int)now.trains));
		_m = 3; goto P999; /* 0 */
	case 34: /* STATE 29 - santa.pml:100 - [printf('Santa goes home to Mrs. Claus\\n')] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][29] = 1;
		Printf("Santa goes home to Mrs. Claus\n");
		_m = 3; goto P999; /* 0 */
	case 35: /* STATE 30 - santa.pml:101 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][30] = 1;
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

