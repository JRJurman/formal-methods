sig Course {
	enrolled : set Person,
	limit : Int,
	waiting : seq Person
}
sig Person{}

fact {
	all c : Course | c.limit >= 0
	all c : Course | #c.enrolled <= c.limit

	all c : Course | some c.waiting => #c.enrolled = c.limit
	all c : Course | no c.enrolled & c.waiting.elems
	all c : Course | #c.waiting = #c.waiting.elems
}

run{some waiting} for 5 but 4 Int, 4 seq
