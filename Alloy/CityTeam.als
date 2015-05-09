some sig City{}
some sig Year{}

some sig Team{
	location : City -> Year
}

some sig Player {
	playsFor : Team -> Year
}

fact {
	all p : Player, y : Year | one p.playsFor 6 
	all t : Teams, y : Year | some playsFor.y.t => one t.location.y
	all t : Team, year, | lone t.location.y
}

fun PlayerLocationByYear [: year] : Player -> 


run{
} for exactly 5 Year, exactly 3 City, exactly 3 Team, exactly 6 Player
