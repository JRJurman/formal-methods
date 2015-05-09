some sig Person {
	friends : set Person,
	enemies : set Person
}

// Everyone is a friend of him or her self.
fact AreOwnFriend {
	all p : Person | 
		p in p.friends
}

// Nobody has someone else as both a friend and an enemy.
fact NoFriendsAreEnemies {
	all p1 : Person | 
		no p1.friends & p1.enemies
}

// No person is his or her own enemy.
assert NotOwnEnemy {
	all p : Person |
		p not in p.enemies
}
check NotOwnEnemy for 8

// The enemies of a person's enemies are friends
// of that person.
fact EnemyOfEnemyIsFriend {
	all p : Person, q : p.enemies {
		q.enemies in p.friends
	}
}

// A person's friends have that person as their
// friend.
fact FriendsAreSymmetric {
	friends = ~friends
}

// A person's enemies have that person as their
// enemy.
fact EnemiesAreSymmetric {
	enemies = ~enemies
}

run {} for exactly 5 Person

// There is exactly one person who is the enemy of
// everyone else.
pred CommonEnemy {
	one p1 : Person | all p2 : Person {
		p1 != p2 => p1 in p2.enemies
	}
}
run CommonEnemy for exactly 5 Person

// Some persons have no friends other than themselves.
pred SomeLonelyPersons {
	some p : Person |
		p = p.friends
}
run SomeLonelyPersons for exactly 5 Person

// If there is a CommonEnemy, then
// there are SomeLonelyPersons
// HINT: Use the predicate names (which are propositions)
//       directly - you don't need any quantification
assert IfCommonEnemyThenSomeLonelyPersons {
	CommonEnemy => SomeLonelyPersons
}
check IfCommonEnemyThenSomeLonelyPersons for 8






