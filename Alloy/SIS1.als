// Course Management System
// whose in it, when is it, where is it


sig Person{}
sig Period{}
sig Room{}

sig Course{
	instructor : lone Person,
	enrolled : set Person,
	where    : one Room,
	when     : some Period
}

fact NoCourseRoomConflicts {
	all disj c1, c2 : Course | 
		// & - intersection
		some c1.when & c2.when => c1.where != c2.where
}

fact NoStudentConflicts {
	all p : Person, disj c1, c2 : Course |
		// && - logical and
		(p in c1.enrolled && p in  c2.enrolled) => no c1.when & c2.when
}



// If a Course has an instructor, that Person cannot be enrolled in the Course. (be careful!)
fact InstructorPersonConflicts {
	all p : Person, c : Course |
		p in c.enrolled => no p & c.instructor
}

// No Person can instruct a Course that has Periods in common with a Course in which he is enrolled.
fact InstructorEnrolledConflicts {
	all p : Person, disj c1, c2 : Course |
		(p in c1.instructor && p in  c2.enrolled) => no c1.when & c2.when
}

// No Person can instruct different Courses that have any Periods in common.
fact InstructorScheduleConflicts {
	all p : Person, disj c1, c2 : Course |
		(p in c1.instructor && p in  c2.instructor) => no c1.when & c2.when
}


run {
	# Course >= 2
	# Period >= 2
	# enrolled >= 2
} for 5
