open util/relation
open util/ternary

one sig PerformTransactionIOD extends InteractionOverviewDiagram {}
/*DecisionNodes*/
one sig DecisionNode1, DecisionNode2 extends DecisionNode {}
one sig PinOK,PinNOK,FirstOrSecondWrongPin,ThirdWrongPin extends Condition {}    
/*Refs*/
one sig IODRef1,IODRef2,IODRef3,IODRef4 extends IODRef {}    
one sig SelectTransaction,EnterDetailsAndVerifyPin,ConcludeTransactionAndPrintReceipt,RetainCardAndNotifyCustomer extends SystemSequenceDiagram {}
/*IODSSD's*/
one sig checkPinTryNumber extends IODSSD {}
one sig Sid1,Sid2,Sid3,Sid4,Sid5 extends SeqDid {}    
/*Messages*/
one sig checkNumberOfWrongPins extends Message {}
/*Lifelines*/
one sig Customer,ATMSystem extends Lifeline {}
/* ************************************ */
fact iod { 
    initialNode = PerformTransactionIOD -> IODRef1
}
fact decisionpoints {  
    // os true e falses estao postos da maneira k reflecte o main flow
    conditions = DecisionNode1 -> 0 -> PinOK +
                DecisionNode1 -> 1 -> PinNOK +
                DecisionNode2 -> 0 -> FirstOrSecondWrongPin +
                DecisionNode2 -> 1 -> ThirdWrongPin 
    
    alt_flow =  DecisionNode1 -> 0 -> IODRef3 +
               DecisionNode1 -> 1 -> checkPinTryNumber +
               DecisionNode2 -> 0 -> FinalNode +
               DecisionNode2 -> 1 -> IODRef4 
}
fact iodssds { 
     IODSSD <: nextNode = checkPinTryNumber -> DecisionNode2
    seqDid = checkPinTryNumber -> Sid1 +

             SelectTransaction -> Sid2 +
             EnterDetailsAndVerifyPin -> Sid3 +
             ConcludeTransactionAndPrintReceipt -> Sid4 +
             RetainCardAndNotifyCustomer -> Sid5 

    system = checkPinTryNumber -> ATMSystem +                 
                                                         
             SelectTransaction -> ATMSystem +
             EnterDetailsAndVerifyPin -> ATMSystem +          
             ConcludeTransactionAndPrintReceipt -> ATMSystem +
             RetainCardAndNotifyCustomer -> ATMSystem         

    actor = checkPinTryNumber -> Customer +                 
                                                        
            SelectTransaction -> Customer +
            EnterDetailsAndVerifyPin -> Customer +          
            ConcludeTransactionAndPrintReceipt -> Customer +
            RetainCardAndNotifyCustomer -> Customer         
    
    messages = checkPinTryNumber -> 0 -> checkNumberOfWrongPins
}
fact iodrefs { 
    IODRef <: reference = IODRef1 -> Sid2 +
                IODRef2 -> Sid3 +
                IODRef3 -> Sid4 +
                IODRef4 -> Sid5

    IODRef <: nextNode = IODRef1 -> IODRef2 +
               IODRef2 -> DecisionNode1 +
               IODRef3 -> FinalNode +
               IODRef4 -> FinalNode
}
fact messages { 
    source = checkNumberOfWrongPins -> ATMSystem

    target = checkNumberOfWrongPins -> ATMSystem
}
/* ************************************ */
run {} for 10 but 5 int
