some sig Person{}

some sig Course {
	enrolled : set Person
}

pred have_stuendents[e : Course] {
	some e.enrolled
}


run {}

run {
	some c : Course | have_stuendents[c]
} for 5
