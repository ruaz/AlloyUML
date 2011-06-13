module umlFormalModels/InteractionOverviewDiagram

open umlFormalModels/SystemSequenceDiagram
open util/boolean
open util/relation
open util/ternary

abstract sig InteractionOverviewDiagram {
	flow: seq IODRef + SystemSequenceDiagram + AltPoint
}

abstract sig AltPoint {
	condition: Bool,
	alt_flow: set (seq Ref + SystemSequenceDiagram + AltPoint)
} {
	AltPoint in univ.(InteractionOverviewDiagram.flow)
	#alt_flow > 1
}
/*fact { all a in alt_flow |*/
/*	   	(seq Ref + SystemSequenceDiagram + AltPoint) in alt_flow}*/
fact { irreflexive[select13[alt_flow]] }

abstract sig IODRef {
	reference: SeqDid
} {
	// pra não haver IODRefs soltos
	IODRef in univ.(InteractionOverviewDiagram.flow)
}
/* ************************************ */
run {} for 5 but exactly 1 InteractionOverviewDiagram, exactly 2
IODRef, exactly 2 AltPoint
