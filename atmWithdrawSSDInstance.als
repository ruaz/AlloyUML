open util/relation
open util/ternary

one sig WithdrawSSD,HandleInvalidPinSSD extends SystemSequenceDiagram {}    
one sig Customer,ATMSystem extends Lifeline {}    
one sig Opt1,Opt2 extends Opt {}    
one sig Loop1 extends Loop {}    
one sig PinOk,isOkTrue,isOkFalse,isOkFalse2 extends Condition {}    
one sig Operand1,Operand2,Operand3 extends Operand {}    
one sig selectWithdraw,requestAccType,enterAccType,requestAmount,enterAmount,enoughMoney,
        notifyAndAskSmallerAmount,checkPin,dispenseCash,printReceipt extends Message {}
one sig Ref1 extends Ref {}    
one sig ssdid1,ssdid2 extends SeqDid {}    

fact ssd { seqDid = WithdrawSSD -> ssdid1 + HandleInvalidPinSSD -> ssdid2
           actor = WithdrawSSD -> Customer + HandleInvalidPinSSD -> Customer
           system = WithdrawSSD -> ATMSystem + HandleInvalidPinSSD -> ATMSystem
            SystemSequenceDiagram <: messages = WithdrawSSD -> 0 -> selectWithdraw +
                      WithdrawSSD -> 1 -> requestAccType +
                      WithdrawSSD -> 2 -> enterAccType +
                      WithdrawSSD -> 3 -> requestAmount +
                      WithdrawSSD -> 4 -> Loop1 +
                      WithdrawSSD -> 5 -> checkPin +
                      WithdrawSSD -> 6 -> Opt2 +
                      WithdrawSSD -> 7 -> dispenseCash +
                      WithdrawSSD -> 8 -> printReceipt 
                      --Operands
            Operand <: messages = Operand1 -> 0 -> enterAmount +
                                  Operand1 -> 1 -> enoughMoney +
                                  Operand1 -> 2 -> Opt1 +

                                  Operand2 -> 0 -> notifyAndAskSmallerAmount +
                                  
                                  Operand3 -> 0 -> Ref1
}
fact frames { 
              Opt <: condition = Opt1 -> isOkFalse + Opt2 -> isOkFalse2
              Loop <: condition = Loop1 -> isOkTrue
              Opt <: operand = Opt1 -> Operand2 + Opt2 -> Operand3 
              Loop <: operand = Loop1 -> Operand1
}
fact refs { reference = Ref1 -> ssdid2 }
fact mensagens { 
    source = selectWithdraw -> Customer +
             requestAccType -> ATMSystem +
             enterAccType -> Customer +
             requestAmount -> ATMSystem +
             enoughMoney -> ATMSystem +
             enterAmount -> Customer +
             notifyAndAskSmallerAmount -> ATMSystem +
             checkPin -> ATMSystem +
             dispenseCash -> ATMSystem +
             printReceipt -> ATMSystem

    target = selectWithdraw -> ATMSystem +             
             requestAccType -> Customer +            
             enterAccType -> ATMSystem +               
             requestAmount -> Customer +             
             enoughMoney -> ATMSystem +
             enterAmount -> ATMSystem +               
             notifyAndAskSmallerAmount -> Customer + 
             checkPin -> ATMSystem +
             dispenseCash -> ATMSystem +
             printReceipt -> ATMSystem
}
