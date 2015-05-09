some sig Person{
	transcript : set Course
}

some sig Course{
	prereqs : set Course,
	enrolled : set Person
}

fact MustHavePrereqs {
	all c : Course {
		all p : c.enrolled {
			c.prereqs in p.transcript
		}
	}
}

fact CannotBeOwnPrereq {
	all c : Course | c not in c.^prereqs
}

run {
	some enrolled
	Course.enrolled != Person
	enrolled.Person != Course
	some c : Course | #c.prereqs = 3
	#Person = 4
}	for 5
