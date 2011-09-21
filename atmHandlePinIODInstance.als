open util/relation
open util/ternary

one sig HandleInvalidPinIOD extends InteractionOverviewDiagram {}
/*DecisionNodes*/
one sig DecisionNode1 extends DecisionNode {}
one sig FirstOrSecondWrongPin,ThirdWrongPin extends Condition {}    
/*Refs*/
one sig IODRef1 extends IODRef {}    
one sig RetainCardAndNotifyCustomer extends SystemSequenceDiagram {}
/*IODSSD's*/
one sig checkPinTryNumber extends IODSSD {}
one sig Sid1,Sid2 extends SeqDid {}    
/*Messages*/
one sig checkNumberOfWrongPins extends Message {}
/*Lifelines*/
one sig Customer,ATMSystem extends Lifeline {}
/* ************************************ */
fact iod { 
    initialNode = HandleInvalidPinIOD -> checkPinTryNumber
}
fact decisionpoints {  
    // os true e falses estao postos da maneira k reflecte o main flow
    conditions = DecisionNode1 -> 0 -> FirstOrSecondWrongPin +
                 DecisionNode1 -> 1 -> ThirdWrongPin 
    
    alt_flow = DecisionNode1 -> 0 -> FinalNode +
               DecisionNode1 -> 1 -> IODRef1 
}
fact iodssds { 
     IODSSD <: nextNode = checkPinTryNumber -> DecisionNode1
    seqDid = checkPinTryNumber -> Sid1 +
             RetainCardAndNotifyCustomer -> Sid2

    system = checkPinTryNumber -> ATMSystem +
             RetainCardAndNotifyCustomer -> ATMSystem

    actor =  checkPinTryNumber -> Customer +
             RetainCardAndNotifyCustomer -> Customer
    
    messages = checkPinTryNumber -> 0 -> checkNumberOfWrongPins
}
fact iodrefs { 
    IODRef <: reference = IODRef1 -> Sid1

    IODRef <: nextNode = IODRef1 -> FinalNode
}
fact messages { 
    source = checkNumberOfWrongPins -> ATMSystem

    target = checkNumberOfWrongPins -> ATMSystem
}
