open util/relation
open util/ternary

one sig PerformSessionSSD,PerformTransactionSSD extends SystemSequenceDiagram {}    
one sig Customer,ATMSystem extends Lifeline {}    
one sig Loop1 extends Loop {}    
one sig Opt1 extends Opt {}    
one sig Break1 extends Break {}    
one sig CardNotOK,OKIsTrue,CustomerWantsMore extends Condition {}    
one sig Operand1,Operand2,Operand3 extends Operand {}    
one sig insertCard,isCardOK,readCard,requestPin,enterPin,requestTransaction,wantAnotherTransaction,selectNo,
        ejectCard,terminateSession,notify,selectYes extends Message {}
one sig Ref1 extends Ref {}    
one sig ssdid1,ssdid2 extends SeqDid {}    

fact ssd { seqDid = PerformSessionSSD -> ssdid1 + PerformTransactionSSD -> ssdid2
           actor = PerformSessionSSD -> Customer + PerformTransactionSSD -> Customer
           system = PerformSessionSSD -> ATMSystem + PerformTransactionSSD -> ATMSystem
            SystemSequenceDiagram <: messages = PerformSessionSSD -> 0 -> insertCard +
                      PerformSessionSSD -> 1 -> isCardOK +
                      PerformSessionSSD -> 2 -> Break1 +
                      PerformSessionSSD -> 3 -> readCard +
                      PerformSessionSSD -> 4 -> requestPin +
                      PerformSessionSSD -> 5 -> enterPin +
                      PerformSessionSSD -> 6 -> Loop1 +
                      PerformSessionSSD -> 7 -> selectNo +
                      PerformSessionSSD -> 8 -> ejectCard +
                      PerformSessionSSD -> 9 -> terminateSession
                      --Operands
            Operand <: messages = Operand1 -> 0 -> ejectCard+
                      Operand1 -> 1 -> notify +

                      Operand2 -> 0 -> requestTransaction +
                      Operand2 -> 1 -> Ref1 +
                      Operand2 -> 2 -> wantAnotherTransaction +
                      Operand2 -> 3 -> Opt1 +

                      Operand3 -> 0 -> selectYes
}
fact frames { Loop <: condition = Loop1 -> OKIsTrue 
              Break <: condition = Break1 -> CardNotOK
              Opt <: condition = Opt1 -> CustomerWantsMore
              Break <: operand = Break1 -> Operand1 
              Loop <: operand = Loop1 -> Operand2 
              Opt <: operand = Opt1 -> Operand3 
}
fact refs { reference = Ref1 -> ssdid2 }
fact mensagens { 
    source = insertCard -> Customer +
             isCardOK -> ATMSystem +
             readCard -> ATMSystem +
             requestPin -> ATMSystem +
             enterPin -> Customer +
             requestTransaction -> ATMSystem +
             wantAnotherTransaction -> ATMSystem +
             selectNo -> Customer +
             ejectCard -> ATMSystem +
             terminateSession -> ATMSystem +
             notify -> ATMSystem +
             selectYes -> Customer

    target = insertCard -> ATMSystem +
             isCardOK -> ATMSystem +
             readCard -> ATMSystem +
             requestPin -> Customer +
             enterPin -> ATMSystem +
             requestTransaction -> Customer +
             wantAnotherTransaction -> Customer +
             selectNo -> ATMSystem +
             ejectCard -> ATMSystem +
             terminateSession -> ATMSystem +
             notify -> Customer +
             selectYes -> ATMSystem
}
