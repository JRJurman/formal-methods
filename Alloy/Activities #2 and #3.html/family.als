abstract sig Person {
	father :	lone Man,
	mother :	lone Woman
}
some sig Man, Woman extends Person{}
one sig Adam extends Man{}
one sig Eve extends Woman{}

/**
	* There are men other than Adam and women other than Eve
	*/

fact BeyondEden {
	some m : Man | 
		m != Adam
	some w : Woman |
		w != Eve
}

/**
  * Neither Adam nor Eve have any parents.
  * Adam and Eve are male and female ancestors,
	* respectively, of everyone else.
*/
fact AdamAndEve {
	all p : (Person - (Adam+Eve)) {
		Adam in p.^father
		Eve in p.^mother
	}

	no (Adam.father + Adam.mother)
	no (Eve.father + Eve.mother)
}

/**
	* Taboo
	*		No person's father is from
	*			that person's mother's paternal ancestors
	*		No person's mother is from
	*			that person's father's maternal ancestors
  */

fact Taboo {
	all p : (Person - (Adam+Eve)) {
		p.father not in p.mother.^father
		p.mother not in p.father.^mother
	}
}

/**
	* No man is one of his own male ancestors.
	* No woman is one of her own female ancestors
	*/
assert NoAncestorCycles {
	all p : Person |
		p not in (p.^mother + p.^father)
}
check NoAncestorCycles for 8

run{} for 6

/**
	* Find solutions where exactly one man and
	*	exactly one woman have no children.
	*/
pred NoKids {
	one m : Man | one w : Woman {
		no m.~father
		no w.~mother
	}
}
run NoKids for 6
