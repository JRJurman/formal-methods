open util/ordering[Person] as po

sig Person {
	fname : FirstName,
	lname : LastName,
	job : Job
}

enum FirstName{Ewan, Donald, Alf, Brian, Charles}
enum LastName{Grady, Jackson, Howard, Ibbotson, Frost}
enum Job {Undertaker, Teacher, Driver, Taxidermist, ConMan}

fun A : Person {
	po/first
}

fun B : Person {
	next[A]
}

fun C : Person{
	next[B]
}

fun E : Person{
	next[C]
}

assert OK {
	E = po/last
}
check OK for 5

fact OneToOne {
	Person.fname = FirstName
	Person.lname = LastName
	Person.job = Job
}

fun leftOf[p : Person] : set Person {
	p.prevs
}
fun rightOf[p: Person] : set Person {
	p.prevs
}

fact F1 {
	let ewan = fname.Ewan, jackson = lname.Jackson, ut = job.Undertaker {
		ewan in leftOf[jackson]
		ewan in rightOf[ut]
		jackson.fname != Donald
		jackson.fname != Donald
	}
}

fact F2 {
	lname.Howard in C
}

fact F3 {
	let ibbot = lname.Ibbotson {
		ibbot.job = Teacher
	}
}

fact F4 {
	let frost = lname.Frost {
		frost.job != Undertaker
		frost.fname != Alf
		frost ! in B			// frost != B
	}
}

fact F5 {
	let alf = fname.Alf {
		alf ! in (B + E)
		alf.job ! in (Taxidermist + Driver)
	}
}

fact F6 {
	let brain = fname.Brian {
		brain.lname ! in (Ibbotson + Jackson)
	}
}

fact F7 {
	let chuck = fname.Charles, frost = lname.Frost {
		chuck.job != Taxidermist
		frost.job != Driver
		E ! in (chuck + frost)
	}
}

run{} for 5















