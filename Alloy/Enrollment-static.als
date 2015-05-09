open util/ordering[Step] as step
sig Step{}

/**
 *	Courses have a set of Persons enrolled, an enrollment limit,
 *	and a set of prerequisite courses.
 */
some sig Course{
	enrolled		: set Person -> Step,
	limit				: Int,
	prereqs			: set Course
}

/**
 *	Persons have a transcript of the courses they've completed.
 */
some sig Person {
	transcript	:	set Course,
}

/**
 *	Function to return the Courses Person p is taking.
 */
fun taking[p : Person, st : Step] : set Course {
	enrolled.st.p 
}

/**
 *	A Person cannot retake a Course.
 *	That is, at the Person is not enrolled in a course
 *	on the transcript).
 */
pred Cannot_Retake_Course[st : Step] {
	no p : Person | some p.transcript & taking[p, st]
}

/**
 *	For a Person to enroll in a Course, the Course's
 *	prerequisites must be on the Person's transcript.
 */
pred Must_Have_Prereqs_To_Enroll[st : Step] {
	all p : Person, c : taking[p, st] {
		c.prereqs in p.transcript
	}
}

/**
 *	The number of Persons enrolled in a Course
 *	cannot exceed the Course's limit.
 */
pred Class_Limit_Enforced[st : Step] {
	all c : Course | #c.enrolled.st <= c.limit
}

/**
 *	The enrollment limit for a Course must be
 *	strictly positive.
 */
fact Class_Limit_Postive {
	all c : Course | c.limit > 0
}

/**
 *	A Course cannot be its own prerequisite, either
 *	directly or indirectly (that is, the prerequisite
 *	graph is a DAG).
 */
fact Cannot_Be_Own_Prerequisite {
	no c : Course | c in c.^prereqs
}

/**
 *	The transcript must be consistent in that for any Course
 *	on a Person's transcript, the Course's prerequisites must
 *	also be on the transcript.
 */
fact Consistent_Transcript {
	all p : Person | p.transcript.prereqs in p.transcript
}

pred Invariant[st : Step] {
	Cannot_Retake_Course[st]
	Must_Have_Prereqs_To_Enroll[st]
	Class_Limit_Enforced[st]
}

pred init[st : Step] {
	st = step/first => no taking[Person, st]
}
assert init_closed {
	all st : Step | init[st] => Invariant[st] 
}

pred init_exists {
	Invariant[step/first]
	init[step/first]
}
check init_closed for 6 but exactly 1 Step

/**
 *	Will eventually show all legal states of up to 4
 *	Courses, up to 5 Persons, with an Int bit width
 *	of 5 (-16 .. 15).
 */
run{} for exactly 4 Course, exactly 5 Person, 5 Int, 6 Step

/**
 *	A restriction on the previous run statement:
 *	+	Some course must be full.
 *	+	Some course with students enrolled has some
 *		prerequisites.
 */
run{
	some c0 : Course | #c0.enrolled = c0.limit
	some c1 : Course | some c1.enrolled && some c1.prereqs
} for exactly 4 Course, exactly 5 Person, 5 Int, 6 Step
