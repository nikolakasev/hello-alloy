abstract sig Object {}

abstract sig Operation {}

sig User, Transaction extends Object {
	by: some Permission
} {
	by.on = this
}

one sig View, Update, Add, Delete extends Operation {}

sig Permission {
	to: one Operation,
	on: one Object
}

fact {
	all p: Permission, u: User | p.on = u implies p in u.by
	all u: User | all disj p1, p2 : u.by | p1.to != p2.to
}

pred show {
	#Permission > 0
}

-- two permissions to the same operation are never owned by the same user 
assert sameOperationImpliesDifferentObject {
    all disj p1, p2: Permission | p1.to = p2.to implies no (p1.on & p2.on & User)
}

check sameOperationImpliesDifferentObject

run show
