module umlFormalModule/ActionBlocks

open util/sequniv
open util/relation


abstract sig ActionBlock {
	actionSteps: seq ActionStep
} {
	#actionSteps > 0
	first[actionSteps] in Input
	Input not in univ.(rest[actionSteps])
	Output not in univ.(butlast[actionSteps])
}

sig Query extends ActionBlock {
	
} {
	last[actionSteps] in Output
	// os passos intermédios só podem ser Assume's
	SystemR not in univ.actionSteps
}

sig Internal extends ActionBlock {
	
} {
	Output not in univ.actionSteps
	some s: SystemR | s in univ.actionSteps
}

sig Service extends ActionBlock {
	
} {
	last[actionSteps] in Output
	Assume not in univ.actionSteps
	some s: SystemR | s in univ.actionSteps
}

sig Validation extends ActionBlock {
	
} {
	some a: Assume | a in univ.actionSteps
	SystemR not in univ.actionSteps
	Output not in univ.actionSteps
}

sig Complete extends ActionBlock {
	
} {
	last[actionSteps] in Output
	some a: Assume | a in univ.actionSteps
	some s: SystemR | s in univ.actionSteps
}

/* ************************************ */
abstract sig ActionStep {
	
}

lone sig Input extends ActionStep {
	
}

lone sig Output extends ActionStep {
	
}

lone sig SystemR extends ActionStep {
	
}

lone sig Assume extends ActionStep {
	
}

/* ************************************ */
run {} for 5 but exactly 1 Validation 
