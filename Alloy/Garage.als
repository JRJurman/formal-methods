/**********************
 ***
 ***	Change this to an equivalent dynamic
 ***	model, with facts (implicit and explicit) turned into
 ***	Step-dependent predicates.
 ***	Add an Invariant that combines all these predicates
 ***	into one overall claim.
 ***
 ***	Then define each of the predicates below, and attach
 ***	appropriate closure assertions and existence predicates.
 ***
 ***	init[st : Step]
 ***		The initial state has no cars in any space in the garage.
 ***
 ***	park[c : Car, st : Step]
 ***		At step 'st', a new car 'c' enters the garage an parks
 ***		in an empty space. No other car of space changes.
 ***		Get the prerequisites right!
 ***
 ***	exit[c : Car, st : Step]
 ***		A car 'c' currently parked exits the garage at
 ***		step 'st'. No other car or space changes.
 ***
 **********************/

open util/ordering[Step] as step
sig Step{}

/**
 * Cars that may be parked in the garage.
 */
some sig Car{}

/**
 * The initial state has no cars in any space in the garage.
 */
pred init[st : Step] {
	all c : Car | c not in Space.parked
}

pred init_invariant {
	all st : Step {
		
	}
}

/**
 * The spaces for cars in the garage.
 * A space is occupied by at most one car.
 */
some sig Space{
	parked : lone Car
}

/**
 * Any given car is parked in at most one space.
 */
pred AtMostOneSpacePerCar[st : Step] {
	all c : Car | lone parked.st.c
}

run { } for 5
