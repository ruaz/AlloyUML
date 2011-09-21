open util/relation
open util/ternary

one sig HandleInvalidPinSSD extends SystemSequenceDiagram {}    
one sig Customer,ATMSystem extends Lifeline {}    
one sig Break1 extends Break {}    
one sig isOkFalse extends Condition {}    
one sig Operand1 extends Operand {}    
one sig checkWrongPin1or2,retainCard,notifyAndTerminateSession extends Message {}
one sig ssdid1 extends SeqDid {}    

fact ssd { seqDid = HandleInvalidPinSSD -> ssdid1
           actor = HandleInvalidPinSSD -> Customer
           system = HandleInvalidPinSSD -> ATMSystem
            SystemSequenceDiagram <: messages = HandleInvalidPinSSD -> 0 -> checkWrongPin1or2 +
                        HandleInvalidPinSSD -> 1 -> Break1
                      --Operands
            Operand <: messages = Operand1 -> 0 -> retainCard +
                                  Operand1 -> 1 -> notifyAndTerminateSession
}
fact frames { 
              Break <: condition = Break1 -> isOkFalse
              Break <: operand = Break1 -> Operand1
}
fact mensagens { 
    source = checkWrongPin1or2 -> ATMSystem +
             retainCard -> ATMSystem +
             notifyAndTerminateSession -> ATMSystem

    target = checkWrongPin1or2 -> ATMSystem +       
             retainCard -> ATMSystem +             
             notifyAndTerminateSession -> Customer 
}
