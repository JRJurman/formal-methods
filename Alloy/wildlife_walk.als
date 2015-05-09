abstract  sig Couple {
	husband : Husband,
	wife : Wife,
	animal : Animal,
	bird : Bird
}

one sig Connor, Carver, Jones, Porter, White extends Couple{}

enum Husband {Tom, Paul, Jim, Mike, Peter}
enum Wife {Olivia, Patricia, Sandra, Joanna, Marjorie}
enum Animal {Fox, Beaver, Coyote, Rabbit, Woodchuck}
enum Bird {WildTurkey, Pheasant, Eagle, Swan, Geese}

fact OneToOne {
	all disj c1, c2 : Couple {
		c1.wife != c2.wife
		c1.husband != c2.husband
	}

	Couple.animal = Animal
	Couple.bird = Bird
}

fact PointOne {
	let c_Tom = Tom.~husband {
		c_Tom.animal = Fox
		c_Tom.wife != Olivia
	}
	let c_Beaver = Beaver.~animal {
		c_Beaver.bird = WildTurkey
	}
}

fact PointTwo {
	Carver.wife = Patricia
	Carver.bird != Pheasant
	let c_Paul = Paul.~husband {
		c_Paul.bird != Eagle
	}
	Jones.animal = Coyote
	White.husband != Jim
}

fact PointThree {
	Porter.bird != Swan
	let c_Tom = Tom.~husband {
		c_Tom.wife != Sandra
	}
	Jones.husband != Tom
	Connor.animal = Rabbit
}

fact PointFour {
	let c_Coyote = Coyote.~animal {
		c_Coyote.bird != Swan
	}
	Connor.husband != Mike
	let c_Mike = Mike.~husband {
		c_Mike.animal != Woodchuck
	}
	let c_Sandra = Sandra.~wife {
		c_Sandra.bird = Geese
	}
}

fact PointFive {
	let c_Peter = Peter.~husband {
		c_Peter.wife = Joanna
		c_Peter.bird != WildTurkey
	}
	Jones.husband != Jim
	let c_Jim = Jim.~husband {
		c_Jim.bird = Pheasant
		c_Jim.animal != Woodchuck
	}
}

fact PointSix {
	White.wife = Marjorie
	let c_Marjorie = Marjorie.~wife {
		c_Marjorie.bird != Swan
	}
	Porter.husband = Paul
	Porter.animal != Beaver
}

run {}
