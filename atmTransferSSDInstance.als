open util/relation
open util/ternary

one sig TransferSSD,HandleInvalidPinSSD extends SystemSequenceDiagram {}    
one sig Customer,ATMSystem extends Lifeline {}    
one sig Opt1 extends Opt {}    
one sig isOkFalse extends Condition {}    
one sig Operand1 extends Operand {}    
one sig selectTransfer,requestData,enterData,checkPin,printReceipt extends Message {}
one sig Ref1 extends Ref {}    
one sig ssdid1,ssdid2 extends SeqDid {}    

fact ssd { seqDid = TransferSSD -> ssdid1 + HandleInvalidPinSSD -> ssdid2
           actor = TransferSSD -> Customer + HandleInvalidPinSSD -> Customer
           system = TransferSSD -> ATMSystem + HandleInvalidPinSSD -> ATMSystem
            SystemSequenceDiagram <: messages = TransferSSD -> 0 -> selectTransfer +
                      TransferSSD -> 1 -> requestData +
                      TransferSSD -> 2 -> enterData +
                      TransferSSD -> 3 -> checkPin +
                      TransferSSD -> 4 -> Opt1 +
                      TransferSSD -> 5 -> printReceipt
                      --Operands
            /*Operand <: messages = Operand1 -> 0 -> Ref1*/
}
fact frames { 
              Opt <: condition = Opt1 -> isOkFalse
              Opt <: operand = Opt1 -> Operand1
}
fact refs { reference = Ref1 -> ssdid2 }
fact mensagens { 
    source = selectTransfer -> Customer +
             requestData -> ATMSystem +
             enterData -> Customer +
             checkPin -> ATMSystem +
             printReceipt -> ATMSystem 

    target = selectTransfer -> ATMSystem + 
             requestData -> Customer + 
             enterData -> ATMSystem +    
             checkPin -> ATMSystem +    
             printReceipt -> ATMSystem 
}
