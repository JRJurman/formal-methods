open util/ordering[Act] as award_order

abstract sig Act {
	country : Country,
	award : Award
}

sig Solo extends Act {}

sig Group extends Act {}

one sig Bobbie_Willins, Bratney_Spires, Smiley_Kinogue extends Solo {}
one sig Six, Spots extends Group {}

enum Country{Austrailia, Canada, Ireland, UK, USA}
enum Award{Best_Act, Best_Album, Best_Newcomer, Best_Single, Best_Video}

fun no1 : Act {
	award_order/first
}

fun no2 : Act {
	next[no1]
}

fun no3 : Act {
	next[no2]
}

fun no4 : Act {
	next[no3]
}

fun no5 : Act {
	next[no4]
}

assert OK {
	no5 = award_order/last
}
check OK for 5

fact OneToOne {
	Act.country = Country
	Act.award = Award
}

fact F1 {
	Bratney_Spires in Bobbie_Willins.nexts
	Bobbie_Willins.award = Best_Video
}

fact F2 {
	Smiley_Kinogue.next in Group
	Smiley_Kinogue.next not in Solo
	Smiley_Kinogue not in no3
}

fact F3 {
	let act_best = award.Best_Act {
		act_best in no5
		act_best.country not in Ireland
	}
}

fact F4 {
	let act_UK = country.UK {
		act_UK in no4
		act_UK in Group
		act_UK.award != Best_Single
	}
}

fact F5 {
	let act_aus = country.Austrailia {
		act_aus.award = Best_Album
		act_aus not in no1
	}
}

fact F6 {
	Six.country = Canada
}

run {}
