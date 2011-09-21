module umlFormalModels/InteractionOverviewDiagram

open umlFormalModels/SystemSequenceDiagram
open util/relation
open util/ternary

abstract sig InteractionOverviewDiagram {
	initialNode: IODRef + IODSSD + DecisionNode
    // possivelmente o initialNode não pode ser um DecisionNode, mas para já fica
} 
// usando 'signature fact', a restrição só era aplicada se existisse um IOD na instancia
// deste modo, força-se também a existência de um IOD
//fact { #initialNode = 1 }


abstract sig DecisionNode {
	conditions: seq Condition,
	alt_flow: seq ( IODRef + IODSSD + DecisionNode + FinalNode)
} {
    // tem de haver pelo menos 2 caminhos alternativos a partir de um DecisionNode
    #alt_flow > 1
    // há tantas condições quantos caminhos possíveis
    #conditions = #alt_flow
    // para não haver DecisionNode's orfãos
	DecisionNode in (InteractionOverviewDiagram.initialNode +
                     DecisionNode.@alt_flow[univ] +
                     IODRef.nextNode + IODSSD.nextNode)
    // o elemento apontado por cada alt_flow tem de ser diferente, senão é o mesmo caminho.
    // implementado como: o tamanho da sequencia é igual ao tamanho do conj. das coisas apontadas
    // por cada elemento da sequência. Se o tamanho do conj. fosse menor significava que havia 
    // elementos da sequênca que apontavam para o mesmo sítio.
    #alt_flow = #univ.alt_flow
}
/*fact { all a in alt_flow |*/
/*	   	(seq Ref + IODSSD + DecisionNode) in alt_flow}*/
/*fact { irreflexive[select13[alt_flow]] }*/

abstract sig IODRef {
	reference: SeqDid, // falta dizer k estes seqdid so podem vir de SystemSequenceDiagram
    nextNode: IODRef + IODSSD + DecisionNode + FinalNode
} {
	// pra não haver IODRefs soltos
	IODRef in (InteractionOverviewDiagram.initialNode + 
                    DecisionNode.alt_flow[univ] +
                    IODRef.@nextNode + IODSSD.nextNode)
}
// o próximo nodo não pode ser ele próprio
fact nextNodeIrreflexive { irreflexive[IODSSD <: nextNode] and irreflexive[IODRef <: nextNode]}

abstract sig IODSSD extends SystemSequenceDiagram{
    nextNode: IODRef + DecisionNode + IODSSD + FinalNode
}
one sig FinalNode {} {
    // tem de haver alguma coisa a ligar ao FinalNode
    FinalNode in univ.(IODSSD <: nextNode + IODRef <: nextNode + DecisionNode.alt_flow)
}
/* ************************************ */
/* Instância para teste */
one sig PerformSessionIOD extends InteractionOverviewDiagram {}
/*DecisionNodes*/
one sig DecisionNode1, DecisionNode2 extends DecisionNode {}
one sig CardOK,CardNOK,Sim,Nao extends Condition {}    
/*Refs*/
one sig IODRef1,IODRef2,IODRef3,IODRef4,IODRef5,IODRef6 extends IODRef {}    
one sig InsertAndVerifyCard,RequestPin,EnterPinAndRequestTransaction,PerformTransaction,TerminateSession,
        SelectNoAndTerminateSession extends SystemSequenceDiagram {}
/*IODSSD's*/
one sig AskForMoreTransactions,CustomerSelectsYes extends IODSSD {}
one sig Sid1,Sid2,Sid3,Sid4,Sid5,Sid6,Sid7,Sid8 extends SeqDid {}    
/*Messages*/
one sig WantAnotherTransaction,SelectYes extends Message {}
/*Lifelines*/
one sig Customer,ATMSystem extends Lifeline {}
/* ************************************ */
fact iod { 
    initialNode = PerformSessionIOD -> IODRef1
}
fact decisionpoints {  
    // os true e falses estao postos da maneira k reflecte o main flow
    conditions = DecisionNode1 -> 0 -> CardOK +
                DecisionNode1 -> 1 -> CardNOK +
                DecisionNode2 -> 0 -> Nao +
                DecisionNode2 -> 1 -> Sim 
    
    alt_flow =  DecisionNode1 -> 0 -> IODRef2 +
               DecisionNode1 -> 1 -> IODRef6 +
               DecisionNode2 -> 0 -> IODRef5 +
               DecisionNode2 -> 1 -> CustomerSelectsYes 
}
fact iodssds { 
     IODSSD <: nextNode = AskForMoreTransactions -> DecisionNode2 + 
               CustomerSelectsYes -> IODRef5
    seqDid = AskForMoreTransactions -> Sid1 +
             CustomerSelectsYes -> Sid2 +

             InsertAndVerifyCard -> Sid3 +
             RequestPin -> Sid4 +
             EnterPinAndRequestTransaction -> Sid5 +
             PerformTransaction -> Sid6 +
             TerminateSession -> Sid7 +
             SelectNoAndTerminateSession -> Sid8

    system = AskForMoreTransactions -> ATMSystem +
             CustomerSelectsYes -> ATMSystem +  

            InsertAndVerifyCard -> ATMSystem +
            RequestPin -> ATMSystem +
            EnterPinAndRequestTransaction -> ATMSystem +
            PerformTransaction -> ATMSystem +
            SelectNoAndTerminateSession -> ATMSystem +
            TerminateSession -> ATMSystem 

    actor = AskForMoreTransactions -> Customer +
            CustomerSelectsYes -> Customer +

            InsertAndVerifyCard -> Customer +
            RequestPin -> Customer +
            EnterPinAndRequestTransaction -> Customer +
            PerformTransaction -> Customer +
            SelectNoAndTerminateSession -> Customer +
            TerminateSession -> Customer 
    
    messages = AskForMoreTransactions -> 0 -> WantAnotherTransaction +
               CustomerSelectsYes -> 0 -> SelectYes
}
fact iodrefs { 
    IODRef <: reference = IODRef1 -> Sid1 +
                IODRef2 -> Sid2 +
                IODRef3 -> Sid3 +
                IODRef4 -> Sid4 +
                IODRef5 -> Sid5 +
                IODRef6 -> Sid6 

    IODRef <: nextNode = IODRef1 -> DecisionNode1 +
               IODRef2 -> IODRef3 +
               IODRef3 -> IODRef4 +
               IODRef4 -> AskForMoreTransactions +
               IODRef5 -> FinalNode +
               IODRef6 -> FinalNode
}
fact messages { 
    source = WantAnotherTransaction -> ATMSystem +
             SelectYes -> Customer

    target = WantAnotherTransaction -> Customer +
             SelectYes -> ATMSystem
}
/* ************************************ */
run {} for 10 but 5 int
