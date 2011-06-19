module umlFormalModels/InteractionOverviewDiagram

open umlFormalModels/SystemSequenceDiagram
open util/boolean
open util/relation
open util/ternary

abstract sig InteractionOverviewDiagram {
	flow: seq IODRef + SystemSequenceDiagram + AltPoint
}

abstract sig AltPoint {
	conditions: seq Bool,
	alt_flow: seq (seq IODRef + SystemSequenceDiagram + AltPoint)
} {
    #conditions = #alt_flow
    #conditions > 0
	AltPoint in univ.(InteractionOverviewDiagram.flow)
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

run {} 
