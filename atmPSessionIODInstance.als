open util/relation
opoen util/ternary

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
