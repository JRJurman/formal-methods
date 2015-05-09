open util/ordering[Foo] as fo

sig Foo{
	bar : Color
}
one sig Foobie extends Foo{}

enum Color {Red, Green, Blue}

fact {
	some s : set univ | fo/last in s
	fo/last = Foobie
}
run{}
