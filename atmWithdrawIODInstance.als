open util/relation
open util/ternary

one sig WithdrawIOD extends InteractionOverviewDiagram {}
/*DecisionNodes*/
one sig DecisionNode1, DecisionNode2,DecisionNode3 extends DecisionNode {}
one sig MoneyOK,MoneyNOK,PinOK,PinNOK,FirstOrSecondWrongPin,ThirdWrongPin extends Condition {}    
/*Refs*/
one sig IODRef1,IODRef2,IODRef3,IODRef4,IODRef5,IODRef6 extends IODRef {}    
one sig SelectWithdraw,ChooseAccType,EnterAmountAndVerifyMoneyOnHand,NotifyAndRequestNewAmount,
        DispenseCashAndReceipt,RetainCardAndNotifyCustomer extends SystemSequenceDiagram {}
/*IODSSD's*/
one sig checkPin,checkPinTryNumber extends IODSSD {}
one sig Sid1,Sid2,Sid3,Sid4,Sid5,Sid6,Sid7,Sid8 extends SeqDid {}    
/*Messages*/
one sig checkPinMessage,checkNumberOfWrongPins extends Message {}
/*Lifelines*/
one sig Customer,ATMSystem extends Lifeline {}
/* ************************************ */
fact iod { 
    initialNode = WithdrawIOD -> IODRef1
}
fact decisionpoints {  
    // os true e falses estao postos da maneira k reflecte o main flow
    conditions = DecisionNode1 -> 0 -> MoneyOK +
                DecisionNode1 -> 1 -> MoneyNOK +
                DecisionNode2 -> 0 -> PinOK +
                DecisionNode2 -> 1 -> PinNOK +
                DecisionNode3 -> 0 -> FirstOrSecondWrongPin +
                DecisionNode3 -> 1 -> ThirdWrongPin 
    
    alt_flow =  DecisionNode1 -> 0 -> checkPin +
               DecisionNode1 -> 1 -> IODRef4 +
               DecisionNode2 -> 0 -> IODRef5 +
               DecisionNode2 -> 1 -> checkPinTryNumber +
               DecisionNode3 -> 0 -> IODRef6 +
               DecisionNode3 -> 1 -> FinalNode
}
fact iodssds { 
     IODSSD <: nextNode = checkPin -> DecisionNode2 + checkPinTryNumber -> DecisionNode3
    seqDid = checkPin -> Sid1 +
             checkPinTryNumber -> Sid2 +

             SelectWithdraw -> Sid3 +
             ChooseAccType -> Sid4 +
             EnterAmountAndVerifyMoneyOnHand -> Sid5 +
             NotifyAndRequestNewAmount -> Sid6 +
             DispenseCashAndReceipt -> Sid7 +
             RetainCardAndNotifyCustomer -> Sid8

    system = checkPin -> ATMSystem +
             checkPinTryNumber -> ATMSystem +                 

             SelectWithdraw -> ATMSystem +
             ChooseAccType -> ATMSystem +
             EnterAmountAndVerifyMoneyOnHand -> ATMSystem +
             NotifyAndRequestNewAmount -> ATMSystem +
             DispenseCashAndReceipt -> ATMSystem +
             RetainCardAndNotifyCustomer -> ATMSystem
                                                         

    actor =  checkPin -> Customer +
             checkPinTryNumber -> Customer +                 
                                                        
             SelectWithdraw -> Customer +
             ChooseAccType -> Customer +
             EnterAmountAndVerifyMoneyOnHand -> Customer +
             NotifyAndRequestNewAmount -> Customer +
             DispenseCashAndReceipt -> Customer +
             RetainCardAndNotifyCustomer -> Customer
    
    messages = checkPin -> 0 -> checkPinMessage + checkPinTryNumber -> 0 -> checkNumberOfWrongPins
}
fact iodrefs { 
    IODRef <: reference = IODRef1 -> Sid3 +
                IODRef2 -> Sid4 +
                IODRef3 -> Sid5 +
                IODRef4 -> Sid6 +
                IODRef5 -> Sid7 +
                IODRef6 -> Sid8

    IODRef <: nextNode = IODRef1 -> IODRef2 +
               IODRef2 -> IODRef3 +
               IODRef3 -> DecisionNode1 +
               IODRef4 -> IODRef3 +
               IODRef5 -> FinalNode +
               IODRef6 -> FinalNode
}
fact messages { 
    source = checkPinMessage -> ATMSystem + checkNumberOfWrongPins -> ATMSystem

    target = checkPinMessage -> ATMSystem + checkNumberOfWrongPins -> ATMSystem
}
/* ************************************ */
run {} for 10 but 5 int
