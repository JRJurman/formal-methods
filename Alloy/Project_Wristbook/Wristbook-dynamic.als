/**
 * The ordered Step set used to order successive states.
 */
open util/ordering[Step] as step
sig Step{}

/**
 *  There is exactly one Wristbook, with one relation accounts: 
 *  the set of Persons who have accounts on the system.
 */

one sig Wristbook {
	accounts : set Person -> Step
}

/**
 * Each person is associated with two sets of Persons: a set of friends and 
 *                                                     a set of incoming friend requests.
 * That is, for a given Person p, p.friends is the set of Persons p lists as friends, 
 * and p.requests is the set of Persons who have requested friendship with p.
 */

some sig Person {
  friends : set Person -> Step,
  requests : set Person -> Step
}

/** If Person a is friends with b, then b is friends with a. */
pred FriendsSymmetric[st : Step] {
	all a, b : Person {
		b in a.friends.st => a in b.friends.st
	}
}

/** 
 * Any Person p who is not in the Wristbook accounts 
 * (a) has no friends, 
 * (b) has no incoming friend requests, and 
 * (c) may not be shown as making any friend requests.
 */
pred NoAccount_NoFriendsOrRequests[st : Step] {
	all p : Person - Wristbook.accounts.st {
		no p.friends.st
		no p.requests.st
		p not in Person.requests.st
	}
}

/**
 * No Person p has incoming friend requests from anyone with whom p is already friends.
 */
pred NoFriendsMakeRequests[st : Step] {
	all p : Person {
		no (p.friends.st & p.requests.st)
	}
}

/**
 * No Person p is friends with him or her self.
 */
pred NotFriendsOfSelf[st : Step] {
	all p : Person {
		p not in p.friends.st
	}
}

/**
 * No Person p has friend requests with him or her self.
 */
pred NoRequestsOfSelf[st : Step] {
	all p : Person {
		p not in p.requests.st
	}
}

/**
 * the conjunction of all the facts-turned-predicates
 */
pred Invariant[st : Step] {
	FriendsSymmetric[st]
	NoAccount_NoFriendsOrRequests[st]
	NoFriendsMakeRequests[st]
	NotFriendsOfSelf[st]
	NoRequestsOfSelf[st]
}

/**
 * The initial state is one where no Person has a Wristbook account;
 * of course, other conditions follow from this statement.
 */
pred init[st : Step] {
	all p : Person | p not in Wristbook.accounts.st
}

pred init_exists {
	Invariant[step/first]
	init[step/first]
}
run init_exists for 6 but exactly 1 Step

assert init_closed {
	all st : Step {
		Invariant[st] && init[st] => Invariant[next[st]]
	}
}
check init_closed for 6 but exactly 1 Step

/**
 * Person p, who is not in Wristbook's accounts at Step st, is in the accounts at the next Step. 
 * Nothing else changes.
 */
pred enroll[st : Step, p : Person] {
	
	//pre-conditions
	p not in Wristbook.accounts.st

	let st' = next[st] {
		
		//effects
		Wristbook.accounts.st' = Wristbook.accounts.st + p
		
		//framing
		all pL : Person {
			pL.friends.st' = pL.friends.st
			pL.requests.st' = pL.requests.st
		}

	}
}

pred enroll_exists {
	some st : Step, p : Person {
		Invariant[st]
		enroll[st, p]
	}
}
run enroll_exists for 4 but 2 Step

assert enroll_closed {
	all st : Step, p : Person {
		Invariant[st] && enroll[st, p] =>
			Invariant[next[st]]
	}
}
check enroll_closed for 6 but 2 Step


/**
 * Person p, who is in Wristbook's accounts at Step st, is not in the accounts at the next Step.
 * The friends and requests relations must be updated to reflect the withdrawal so as to maintain the Invariant.
 */
pred withdraw[st : Step, p : Person] {

	//pre-conditions
	p in Wristbook.accounts.st

	let st' = next[st] {

		//effects
		Wristbook.accounts.st' = Wristbook.accounts.st - p
		no p.friends.st'
		no p.requests.st'
		all pL : Person {
			pL.friends.st' = pL.friends.st - p
			pL.requests.st' = pL.requests.st - p
		}

	}
}

pred withdraw_exists {
	some st : Step, p : Person {
		Invariant[st]
		withdraw[st, p]
	}
}
run enroll_exists for 4 but 2 Step

assert withdraw_closed {
	all st : Step, p : Person {
		Invariant[st] && withdraw[st, p] =>
			Invariant[next[st]]
	}
}
check withdraw_closed for 6 but 2 Step

/**
 * Person from_p requests friendship with Person to_p; 
 * of course the request must abide by the Wristbook rules about who may request friendship with whom. 
 * If the request is allowable, the only thing that changes is the set of to_p's requests.
 */
pred request[st : Step, from_p, to_p : Person] {

	//pre-conditions
	from_p not in (to_p.friends.st + to_p.requests.st)
	from_p != to_p
	(from_p + to_p) in Wristbook.accounts.st

	let st' = next[st] {

		//effects
		to_p.requests.st' = to_p.requests.st + from_p

		//framing
		Wristbook.accounts.st' = Wristbook.accounts.st
		to_p.friends.st' = to_p.friends.st
		all pL : Person - to_p {
			pL.friends.st' = pL.friends.st
			pL.requests.st' = pL.requests.st
		}

	}
}

pred request_exists {
	some st : Step, from_p, to_p : Person {
		Invariant[st]
		request[st, from_p, to_p]
	}
}
run request_exists for 4 but 2 Step

assert request_closed {
	all st : Step, from_p, to_p : Person {
		Invariant[st] && request[st, from_p, to_p] =>
			Invariant[next[st]]
	}
}
check request_closed for 6 but 2 Step

/**
 * Person to_p accepts the existing request from from_p. 
 * At the end, to_p and from_p are friends, and from_p is removed from to_p's requests (and, if necessary, vice-versa); 
 * nothing else changes. 
 * Of course this assumes the acceptance abides by the Wristbook rules for requests and friends.
 */
pred accept[st : Step, from_p, to_p : Person] {

	//pre-conditions
	from_p in to_p.requests.st
	from_p != to_p

	let st' = next[st] {

		//effects
		from_p.friends.st' = from_p.friends.st + to_p
		to_p.friends.st' = to_p.friends.st + from_p
		from_p.requests.st' = from_p.requests.st - to_p
		to_p.requests.st' = to_p.requests.st - from_p
		

		//framing
		Wristbook.accounts.st' = Wristbook.accounts.st
		all pL : Person - (to_p + from_p) {
			pL.friends.st' = pL.friends.st
			pL.requests.st' = pL.requests.st
		}

	}
}

pred accept_exists {
	some st : Step, from_p, to_p : Person {
		Invariant[st]
		accept[st, from_p, to_p]
	}
}
run accept_exists for 4 but 2 Step

assert accept_closed {
	all st : Step, from_p, to_p : Person {
		Invariant[st] && accept[st, from_p, to_p] =>
			Invariant[next[st]]
	}
}
check accept_closed for 6 but 2 Step

/**
 * Person to_p denies the existing request from from_p;
 * to be reasonable, to_p cannot be requesting friendship with from_p.
 * At the end, from_p is removed from to_p's requests;
 * nothing else changes. 
 * Of course this assumes the denial abides by the Wristbook rules for requests and friends.
 */
pred deny[st : Step, from_p, to_p : Person] {

	//pre-conditions
	to_p not in from_p.requests.st
	from_p in to_p.requests.st

	let st' = next[st] {

		//effects
		to_p.requests.st' = to_p.requests.st - from_p

		//framing
		Wristbook.accounts.st' = Wristbook.accounts.st
		to_p.friends.st' = to_p.friends.st
		all pL : Person - to_p {
			pL.friends.st' = pL.friends.st
			pL.requests.st' = pL.requests.st
		}

	}
}

pred deny_exists {
	some st : Step, from_p, to_p : Person {
		Invariant[st]
		deny[st, from_p, to_p]
	}
}
run deny_exists for 4 but 2 Step

assert deny_closed {
	all st : Step, from_p, to_p : Person {
		Invariant[st] && deny[st, from_p, to_p] =>
			Invariant[next[st]]
	}
}
check deny_closed for 6 but 2 Step

/**
 * Person p de-friends the existing friend unf_p. At the end, the two Persons are no longer friends; 
 * nothing else changes. 
 * Of course this assumes the de-friending abides by the Wristbook rules for requests and friends.
 */
pred de_friend[st : Step, p, unf_p : Person] {

	//pre-conditions
	unf_p in p.friends.st

	let st' = next[st] {

		//effects
		p.friends.st' = p.friends.st - unf_p
		unf_p.friends.st' = unf_p.friends.st - p

		//framing
		Wristbook.accounts.st' = Wristbook.accounts.st
		p.requests.st' = p.requests.st
		unf_p.requests.st' = unf_p.requests.st
		all pL : Person - (p + unf_p) {
			pL.friends.st' = pL.friends.st
			pL.requests.st' = pL.requests.st
		}

	}
}


pred de_friend_exists {
	some st : Step, p, unf_p : Person {
		Invariant[st]
		de_friend[st, p, unf_p]
	}
}
run de_friend_exists for 4 but 2 Step

assert de_friend_closed {
	all st : Step, p, unf_p : Person {
		Invariant[st] && de_friend[st, p, unf_p] =>
			Invariant[next[st]]
	}
}
check de_friend_closed for 6 but 2 Step
