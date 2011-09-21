open util/relation
open util/ternary

one sig TransferIOD extends InteractionOverviewDiagram {}
/*DecisionNodes*/
one sig DecisionNode1,DecisionNode2 extends DecisionNode {}
one sig PinOK,PinNOK,FirstOrSecondWrongPin,ThirdWrongPin extends Condition {}    
/*Refs*/
one sig IODRef1,IODRef2,IODRef3 extends IODRef {}    
one sig SelectTransfer,EnterDataAndVerifyPin,RetainCardAndNotifyCustomer extends SystemSequenceDiagram {}
/*IODSSD's*/
one sig printReceipt,checkPinTryNumber extends IODSSD {}
one sig Sid1,Sid2,Sid3,Sid4,Sid5 extends SeqDid {}    
/*Messages*/
one sig printReceiptMessage,checkNumberOfWrongPins extends Message {}
/*Lifelines*/
one sig Customer,ATMSystem extends Lifeline {}
/* ************************************ */
fact iod { 
    initialNode = TransferIOD -> IODRef1
}
fact decisionpoints {  
    // os true e falses estao postos da maneira k reflecte o main flow
    conditions = DecisionNode1 -> 0 -> PinOK +
                DecisionNode1 -> 1 -> PinNOK +
                DecisionNode2 -> 0 -> FirstOrSecondWrongPin +
                DecisionNode2 -> 1 -> ThirdWrongPin 
    
    alt_flow =  DecisionNode1 -> 0 -> printReceipt +
               DecisionNode1 -> 1 -> checkPinTryNumber +
               DecisionNode2 -> 0 -> FinalNode +
               DecisionNode2 -> 1 -> IODRef3 
}
fact iodssds { 
     IODSSD <: nextNode = printReceipt -> FinalNode + checkPinTryNumber -> DecisionNode2
    seqDid = printReceipt -> Sid1 +
             checkPinTryNumber -> Sid2 +

             SelectTransfer -> Sid3 +
             EnterDataAndVerifyPin -> Sid4 +
             RetainCardAndNotifyCustomer -> Sid5

    system = printReceipt -> ATMSystem +
             checkPinTryNumber -> ATMSystem +                 

             SelectTransfer -> ATMSystem + 
             EnterDataAndVerifyPin -> ATMSystem + 
             RetainCardAndNotifyCustomer -> ATMSystem

    actor =  printReceipt -> Customer +
             checkPinTryNumber -> Customer +                 
                                                        
             SelectTransfer -> Customer + 
             EnterDataAndVerifyPin -> Customer + 
             RetainCardAndNotifyCustomer -> Customer
    
    messages = printReceipt -> 0 -> printReceiptMessage + checkPinTryNumber -> 0 -> checkNumberOfWrongPins
}
fact iodrefs { 
    IODRef <: reference = IODRef1 -> Sid3 +
                IODRef2 -> Sid4 +
                IODRef3 -> Sid5

    IODRef <: nextNode = IODRef1 -> IODRef2 +
               IODRef2 -> DecisionNode1 +
               IODRef3 -> FinalNode
}
fact messages { 
    source = printReceiptMessage -> ATMSystem + checkNumberOfWrongPins -> ATMSystem

    target = printReceiptMessage -> ATMSystem + checkNumberOfWrongPins -> ATMSystem
}
