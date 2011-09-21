open util/relation
open util/ternary

one sig PerformTransactionSSD,HandleInvalidPin extends SystemSequenceDiagram {}    
one sig Customer,ATMSystem extends Lifeline {}    
one sig Opt1 extends Opt {}    
one sig PinOk extends Condition {}    
one sig Operand1 extends Operand {}    
one sig selectTransaction,requestDetails,enterDetails,checkPin,performAdequateSteps,printReceipt extends Message {}
one sig Ref1 extends Ref {}    
one sig ssdid1,ssdid2 extends SeqDid {}    

fact ssd { seqDid = PerformTransactionSSD -> ssdid1 + HandleInvalidPin -> ssdid2
           actor = PerformTransactionSSD -> Customer + HandleInvalidPin -> Customer
           system = PerformTransactionSSD -> ATMSystem + HandleInvalidPin -> ATMSystem
            SystemSequenceDiagram <: messages = PerformTransactionSSD -> 0 -> selectTransaction +
                      PerformTransactionSSD -> 1 -> requestDetails +
                      PerformTransactionSSD -> 2 -> enterDetails +
                      PerformTransactionSSD -> 3 -> checkPin +
                      PerformTransactionSSD -> 4 -> Opt1 +
                      PerformTransactionSSD -> 5 -> performAdequateSteps +
                      PerformTransactionSSD -> 6 -> printReceipt
                      --Operands
            Operand <: messages = Operand1 -> 0 -> Ref1 
}
fact frames { 
              Opt <: condition = Opt1 -> PinOk
              Opt <: operand = Opt1 -> Operand1 
}
fact refs { reference = Ref1 -> ssdid2 }
fact mensagens { 
    source = selectTransaction -> Customer +
             requestDetails -> ATMSystem +
             enterDetails -> Customer +
             checkPin -> ATMSystem +
             performAdequateSteps -> ATMSystem +
             printReceipt -> ATMSystem

    target = selectTransaction -> ATMSystem +
             requestDetails -> Customer +
             enterDetails -> ATMSystem +
             checkPin -> ATMSystem +
             performAdequateSteps -> ATMSystem +
             printReceipt -> ATMSystem
}
