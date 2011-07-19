module umlFormalModels/InteractionOverviewDiagram

open umlFormalModels/SystemSequenceDiagram
open util/boolean
open util/relation
open util/ternary

abstract sig InteractionOverviewDiagram {
	initialNode: IODRef + IODSSD + DecisionNode
    // possivelmente o initialNode não pode ser um DecisionNode, mas para já fica
}

abstract sig DecisionNode {
	conditions: seq Bool,
	alt_flow: seq ( IODRef + IODSSD + DecisionNode)
} {
    #conditions = #alt_flow
    #conditions > 0
	/*DecisionNode in univ.(InteractionOverviewDiagram.flow)*/
}
/*fact { all a in alt_flow |*/
/*	   	(seq Ref + IODSSD + DecisionNode) in alt_flow}*/
/*fact { irreflexive[select13[alt_flow]] }*/

abstract sig IODRef {
	reference: SeqDid, // falta dizer k estes seqdid so podem vir de SystemSequenceDiagram
    nextNode: IODRef + IODSSD + DecisionNode + FinalNode
} {
	// pra não haver IODRefs soltos
	/*IODRef in univ.(InteractionOverviewDiagram.flow)*/
}
sig IODSSD extends SystemSequenceDiagram{
    nextNode: IODRef + DecisionNode + IODSSD + FinalNode
}
one sig FinalNode {}
/* ************************************ */
/* Instância para teste */
one sig InteractionOverviewDiagram1 extends InteractionOverviewDiagram {}
one sig DecisionNode1, DecisionNode2, DecisionNode3, DecisionNode4 extends DecisionNode {}
one sig IODRef1, IODRef2, IODRef3, IODRef4 extends IODRef {}
one sig IODSSD1, IODSSD2, IODSSD3, IODSSD4, IODSSD5 extends IODSSD {}
one sig SystemSequenceDiagram1, SystemSequenceDiagram2, SystemSequenceDiagram3, SystemSequenceDiagram4 extends SystemSequenceDiagram {}
one sig Query1, ChooseProduct, SubmitPayInfo, CarryOutPay, SeqDid1, SeqDid2, SeqDid3, SeqDid4, SeqDid5 extends SeqDid {}
one sig Actor, System extends Lifeline {}
one sig ChoosesCat, ShowRes, ShowPurchaseSum, ChoosesProd, SubmitPInfo, CarryOutPayment, ProductUnavailable, ProvideConfirmationNumber,
        RepeatSearch, Cancel, PaymentNOK extends Message {}
/* ************************************ */
fact iod { 
    initialNode = InteractionOverviewDiagram1 -> IODRef1
}
fact decisionpoints {  
    // os true e falses estao postos da maneira k reflecte o main flow
    conditions = DecisionNode1 -> 0 -> True +
                DecisionNode1 -> 1 -> False +
                DecisionNode2 -> 0 -> True +
                DecisionNode2 -> 1 -> False +
                DecisionNode3 -> 0 -> True +
                DecisionNode3 -> 1 -> False +
                DecisionNode4 -> 0 -> True +
                DecisionNode4 -> 1 -> False 
    
    alt_flow =  DecisionNode1 -> 0 -> IODRef2 +
               DecisionNode1 -> 1 -> IODSSD2 +
               DecisionNode2 -> 0 -> IODSSD1 +
               DecisionNode2 -> 1 -> IODSSD3 +
               DecisionNode3 -> 0 -> IODRef3 +
               DecisionNode3 -> 1 -> IODSSD4 +
               DecisionNode4 -> 0 -> IODRef4 +
               DecisionNode4 -> 1 -> IODSSD5
}
fact iodssds { 

      IODSSD <: nextNode = IODSSD1 -> DecisionNode3 + 
               IODSSD2 -> IODRef1 + 
               IODSSD3 -> FinalNode + 
               IODSSD4 -> FinalNode +
               IODSSD5 -> IODRef3 
    seqDid = SystemSequenceDiagram1 -> Query1 +
             SystemSequenceDiagram2 -> ChooseProduct +
             IODSSD1 -> SeqDid1 +
             SystemSequenceDiagram3 -> SubmitPayInfo +
             SystemSequenceDiagram4 -> CarryOutPay +
             IODSSD2 -> SeqDid2 +
             IODSSD3 -> SeqDid3 +
             IODSSD4 -> SeqDid4 +
             IODSSD5 -> SeqDid5 

    system = IODSSD1 -> System +
             IODSSD2 -> System +
             IODSSD3 -> System +
             IODSSD4 -> System +
             IODSSD5 -> System +
             SystemSequenceDiagram1 -> System +
             SystemSequenceDiagram2 -> System +
             SystemSequenceDiagram3 -> System +
             SystemSequenceDiagram4 -> System 

    actor = IODSSD1 -> Actor +
            IODSSD2 -> Actor +
            IODSSD3 -> Actor +
            IODSSD4 -> Actor +
            IODSSD5 -> Actor +
            SystemSequenceDiagram1 -> Actor +
            SystemSequenceDiagram2 -> Actor +
            SystemSequenceDiagram3 -> Actor +
            SystemSequenceDiagram4 -> Actor 
    
    messages = SystemSequenceDiagram1 -> 0 -> ChoosesCat +
               SystemSequenceDiagram1 -> 1 -> ShowRes +
               SystemSequenceDiagram2 -> 0 -> ChoosesProd +
               IODSSD1 -> 0 -> ShowPurchaseSum +
               SystemSequenceDiagram3 -> 0 -> SubmitPInfo +
               SystemSequenceDiagram4 -> 0 -> CarryOutPayment +
               SystemSequenceDiagram4 -> 1 -> ProvideConfirmationNumber +
               IODSSD2 -> 0 -> RepeatSearch +
               IODSSD3 -> 0 -> ProductUnavailable +
               IODSSD4 -> 0 -> Cancel +
               IODSSD5 -> 0 -> PaymentNOK
}
fact iodrefs { 
    reference = IODRef1 -> Query1 +
                IODRef2 -> ChooseProduct +
                IODRef3 -> SubmitPayInfo +
                IODRef4 -> CarryOutPay


    IODRef <: nextNode = IODRef1 -> DecisionNode1 +
               IODRef2 -> DecisionNode2 +
               IODRef3 -> DecisionNode4 +
               IODRef4 -> FinalNode 
}
fact messages { 
    source = ShowPurchaseSum -> System +
             RepeatSearch -> Actor +
             ProductUnavailable -> System + 
             Cancel -> Actor +
             PaymentNOK -> System +
             ChoosesCat -> Actor +
             ShowRes -> System +
             ChoosesProd -> Actor +
             SubmitPInfo -> Actor + 
             CarryOutPayment -> System +
             ProvideConfirmationNumber -> System

    target = ShowPurchaseSum -> Actor +
             RepeatSearch -> System +
             ProductUnavailable -> Actor + 
             Cancel -> System +
             PaymentNOK -> Actor +
             ChoosesCat -> System +
             ShowRes -> Actor +
             ChoosesProd -> Sysmem +
             SubmitPInfo -> System + 
             CarryOutPayment -> System +
             ProvideConfirmationNumber -> Actor
}
/* ************************************ */
run {} for 20 but 5 int 
