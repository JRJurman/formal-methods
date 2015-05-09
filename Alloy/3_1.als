sig Course {
	enrolled : set Person
}
sig Person{}

fact EveryoneInAtLeastOneCourse {
	all p : Person | some enrolled.p
	
	all p : Person | some p.~enrolled

	let taking = ~enrolled {
		all p : Person | some p.taking
	}

	all p : Person{	
		let watcha_taking = ~enrolled | some p.watcha_taking
	}
	all p : Person | some p.taking
}

fun  taking : Person -> Course {
	~enrolled
}

fun whatch_taking[p: Person] : set Course {
	p.taking
}

run{}
