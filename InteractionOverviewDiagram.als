module umlFormalModels/InteractionOverviewDiagram

open umlFormalModels/SystemSequenceDiagram
open util/relation
open util/ternary

abstract one sig InteractionOverviewDiagram {
	initialNode: one (IODRef + IODSSD + DecisionNode)
    // (possivelmente o initialNode não pode ser um DecisionNode)
} 
/* ************************************ */
/* Decision Node */
abstract sig DecisionNode {
	conditions: seq Condition,
	alt_flow: seq ( IODRef + IODSSD + DecisionNode + FinalNode)
} {
    // tem de haver pelo menos 2 caminhos alternativos a partir de um DecisionNode
    #alt_flow > 1
    // há tantas condições quantos caminhos possíveis
    #conditions = #alt_flow
    // para não haver DecisionNode's orfãos
	this in (InteractionOverviewDiagram.initialNode +
                     DecisionNode.@alt_flow[Int] +
                     IODRef.nextNode + IODSSD.nextNode)
    // o elemento apontado por cada alt_flow tem de ser diferente, senão é o mesmo caminho.
    // implementado como: o tamanho da sequencia é igual ao tamanho do conj. das coisas apontadas
    // por cada elemento da sequência. Se o tamanho do conj. fosse menor significava que havia 
    // elementos da sequênca que apontavam para o mesmo sítio.
    #alt_flow = #Int.alt_flow
}
/* ************************************ */
/* Refs e SSDs */
abstract sig IODRef {
	reference: one SeqDid, 
    nextNode: one (IODRef + IODSSD + DecisionNode + FinalNode)
} {
	// pra não haver IODRefs soltos
	this in (InteractionOverviewDiagram.initialNode + 
                    DecisionNode.alt_flow[Int] +
                    IODRef.@nextNode + IODSSD.nextNode)
}

/*SSDs */
abstract sig IODSSD extends SystemSequenceDiagram{
    nextNode: one (IODRef + DecisionNode + IODSSD + FinalNode)
}

// o próximo nodo não pode ser ele próprio
fact nextNodeIrreflexive { irreflexive[IODSSD <: nextNode] and irreflexive[IODRef <: nextNode]}
/* ************************************ */
/*Final Node */
one sig FinalNode {} {
    // tem de haver algum nodo a ligar ao FinalNode
    this in univ.(IODSSD <: nextNode + IODRef <: nextNode + DecisionNode.alt_flow)
}
