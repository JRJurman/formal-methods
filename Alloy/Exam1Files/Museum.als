/**
 * The pictures in a museum.
 */
some sig Picture{}

/**
 * Clients of the museum, in general, have some pictures loaned
 * to them and have desires for other pictures.
 */
some sig Client {
	loaned :	set Picture,
	desires	:	set Picture
}

/**
 * The museum has some pictures on display that can be loaned and
 * others in the permanent collection that must remain in the museum.
 *
 * Note: The Pictures on loan are exactly those all the Clients as
 *				a group have been "loaned".
 */
one sig Museum {
	permanent	: set Picture,
	onDisplay	: set Picture
}

/**
 *	All pictures are either on display and loaned out.
 */
fact F1_All_pictures_onDisplay_or_on_loan {
	all p : Picture |
		p in Client.loaned => p not in Museum.onDisplay
	all p : Picture |
		p not in Client.loaned => p in Museum.onDisplay
}

assert PictureSomewhere {
	one p : Picture {
		p in {Client.loaned + Museum.onDisplay}
	}
}
check PictureSomewhere for 8

/**
 *	All pictures in the permanent collection are always on display
 *	(they cannot be loaned to clients).
 *	Pictures on display other than the permanent collection are
 *	eligible for loaning to clients.
 */
fact F2_All_pictures_permanent_are_onDisplay {
	all p : Picture |
		p in Museum.permanent => p in Museum.onDisplay
	all p : Picture |
		p in Museum.permanent => p not in Client.loaned
}

/**
 *	A picture cannot be both on display and loaned out.
 */
fact F3_No_picture_onDisplay_and_loaned {
	all p : Picture |
		p in Client.loaned => p not in Museum.onDisplay
	all p : Picture |
		p in Museum.onDisplay => p not in Client.loaned 
}

/**
 *	No client can desire to borrow pictures that are
 *	in the permanent collection.
 */
fact F4_Client_cannot_desire_permanent_pictures {
	all p : Picture |
		p in Client.desires => p not in Museum.permanent
}	

/**
 *	A client cannot desire a picture he or she has been loaned.
 */
fact F5_Cannot_desire_what_you_are_loaned {
	all c : Client |
		all p : c.desires |
			p not in c.loaned
}

/**
 *	All pictures some client desires are on loan.
 *	Note that a client *MAY* have been loaned a picture
 *	that no other client desires.
 */
fact F6_All_desired_pictures_are_loaned {
	all p : Picture |
		p in Client.desires => p in Client.loaned
}

/**
 *	Two different clients cannot be loaned the same picture.
 */
fact F7_No_loan_conflicts {
	all p : Picture |
		all disj c1, c2 : Client |
			p in c1.loaned => p not in c2.loaned
}

/**
 *	This run predicate is designed to show
 *	"interesting" states.
 */
run{
	some permanent
	some onDisplay - permanent
	some desires
	some loaned
	some Client.loaned - Client.desires
	some Client.loaned & Client.desires
	some loaned.Picture & desires.Picture
} for exactly 3 Client, exactly 8 Picture
