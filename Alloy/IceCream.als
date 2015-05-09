/*
 * Persons are ordered, so there is a first, second, etc.
 * The ordering represents their position in the waiting line.
 * po/first is the person to be served next.
 */
open util/ordering[Person] as po

/*
 * Each person has a scoop of ice cream they want on their cone.
 */
abstract sig Person {
	scoop : IceCream
}

/*
 * The names of the four girls ordering ice cream.
 */
one sig Bridget, Glenda, Patricia, Viola extends Person{}

/*
 * The four types of ice cream the girls want.
 */
enum IceCream {Cherry, Coconut, Peppermint, Vanilla}

/*
 * Four helper functions to indicate the first through
 * fourth girl in line.
 */
fun firstP : Person {
	po/first
}

fun secondP : Person {
  next[firstP]
}

fun thirdP : Person {
  next[secondP]
}

fun fourthP : Person {
  next[thirdP]
}

/*
 * Each flavor is the scoop wanted by exactly
 * one of the girls.
 */
fact OneToOne {
  all disj p1, p2 : Person {
		p1.scoop != p2.scoop
	}
}

/*
 * Fact #1
 *  The second person in line is either Glenda or 
 *  the person who ordered a scoop of Peppermint.
 */
fact F1 {
  let secP = secondP {
		(secP = Glenda) or (secP.scoop = Peppermint)
	}
}

/*
 * Fact #2
 *  The four customers are exactly (1) the second person in line, 
 *  (2) Glenda, (3) Bridget and (4) the person who ordered a Vanilla scoop.
 */
fact F2 {
  let vScoop = scoop.Vanilla {
		secondP ! in (Glenda + Bridget + vScoop)
		vScoop ! in (Glenda + Bridget + secondP)
	}
}

/*
 * Fact #3
 *  Viola was 2 spots in line behind 
 *  the person who ordered a scoop of Coconut.
 */
fact F3 {
  let coScoop = scoop.Coconut {
		Viola in coScoop.next.next
	}
}

/*
 * Fact #4
 * Glenda ordered a scoop of Cherry ice cream.
 */
fact F4 {
  let chScoop = scoop.Cherry {
		Glenda in chScoop
  }
}

/*
 * Run command - correct facts lead to a unique solution.
 */
run {} for 4

