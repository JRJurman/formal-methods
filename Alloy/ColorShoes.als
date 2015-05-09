abstract  sig FName {
	last : LName,
	shoe : Shoe,
	color : Color
}

one sig Clarisse, Margaret, Nancy, Sally extends FName{}

enum LName {Barlow, Parker, Stevens, West}
enum Shoe {Boots, Flats, Pumps, Sandals}
enum Color  {Black, Brown, Green, Pink}

fact OneToOne {
	all disj fn1, fn2 : FName | fn1.last != fn2.last

	FName.shoe = Shoe
	FName.color = Color
}

fact F1 {
	Nancy.shoe != Boots
	Nancy.last = Barlow
}

fact F2 {
	Sally.shoe = Pumps
	let w_parker = Parker.~last {
		w_parker.color = Green
	}
}

fact F3 {
	let w_pumps = Pumps.~shoe {
		w_pumps.color != Pink
	}
}

fact F4 {
	let w_boots = Boots.~shoe {
		w_boots.color = Brown
		w_boots.last != West
	}
}

fact F5 {
	Sally.last != Stevens
	Clarisse.shoe != Flats
}

fact F6 {
	Margaret.last != Parker
	Margaret.shoe = Sandals
	shoe.Sandals.color != Black
}













run{}
