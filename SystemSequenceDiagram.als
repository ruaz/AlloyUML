module umlFormalModels/SystemSequenceDiagram

open util/relation

/* System Sequence Diagram */
abstract sig SystemSequenceDiagram {
	seqDid: SeqDid, 
	system: Lifeline,
	actor: Lifeline,
	messages: seq Message + Frame + Ref,
    /*ucLink: lone UCName // apenas para efeitos de verificação de consistência*/
} {
	system not in actor // actor e sistema são duas lifelines diferentes
	/*#messages > 0 // não permite DS vazios*/ --facto comentado para permitir inclusoes de dummy ssd's
	/*lone messages.conditions.True[univ] (facto apagado por ja não haver bools)*/
    // as mensagens trocadas num dado SSD tem as mesmas lifelines que esse SSD
    (messages[univ].source + messages[univ].target) in (system + actor)
}
// relação de 1-1 entre SystemSequenceDiagram e seqDid
fact { bijective[seqDid, SeqDid] }
// não pode haver referências cíclicas
fact { acyclic[referencia, SystemSequenceDiagram] } 

abstract sig SeqDid {}
/* ******************************** */
/* Lifeline */
abstract sig Lifeline {} { 
	// não há lifelines "soltas", ou são actores ou o sistema
	Lifeline in SystemSequenceDiagram.system + SystemSequenceDiagram.actor
}
/* ******************************** */
/* Message */
abstract sig Message {
	source: Lifeline,
	target: Lifeline
} {
	// não há mensagens "soltas"
	Message in SystemSequenceDiagram.messages[univ] + Operand.messages[univ]
}
/* ******************************** */
/* Ref */
abstract sig Ref {
	reference: SeqDid
} {
	// não há Refs "soltos"
	Ref in SystemSequenceDiagram.messages[univ] + Operand.messages[univ]
}

/* ******************************** */
/* Frame */
abstract sig Frame {} {
	Frame in SystemSequenceDiagram.messages[univ] + Operand.messages[univ]
}

/* Alt */
abstract sig Alt extends Frame {
	conditions: seq Condition, // não sei se Bool será a melhor representação
						  // das condições
	operands: seq Operand
} {
	#conditions = #operands
	#conditions > 0
}

/* Opt */
abstract sig Opt extends Frame  {
	condition: Condition,
	operand: Operand
}

/* Break */
abstract sig Break extends Frame  {
	condition: Condition,
	operand: Operand
}

/* Loop */
abstract sig Loop extends Frame  {
	condition: Condition,
	operand: Operand,
	minint: Int,
	maxint: Int
} {
	minint <= maxint
	minint > 0
}

/* Operand */
abstract sig Operand {
	messages: seq Message + Frame + Ref
} {
	// não há operandos "soltos"
	Operand in Opt.operand + Break.operand + Loop.operand + Alt.operands[univ]
}
abstract sig Condition {}
/* ******************************** */
/* Helper Functions */
fun referencia : SystemSequenceDiagram -> SystemSequenceDiagram {
	{ sd1,sd2 : SystemSequenceDiagram | sd2.seqDid in sd1.messages.reference[univ] }
}
fun framePaiParaFrameFilho : Frame -> Frame {
    { frameP,frameF: Frame | frameF in (frameP.(Opt <: operand).messages[univ] +
                                        frameP.(Break <: operand).messages[univ] +
                                        frameP.(Loop <: operand).messages[univ] +
                                        frameP.operands[univ].messages[univ])}
}
/* ******************************** */
/* Helper Facts */
// se um DSS é referenciado por outro, então tem o mesmo actor e sistema que o que o referencia
fact { all sd1,sd2 : SystemSequenceDiagram | sd1 -> sd2 in referencia 
		=> sd2.actor in sd1.actor && sd2.system in sd1.system }
/*// o actor de um DSS não pode ser o sistema de outro e vice-versa*/
fact { all sd1,sd2 : SystemSequenceDiagram | sd1.actor not in sd2.system }
/*// não é possível encontrar um frame dentro de si próprio*/
fact framesPaiFilhoAciclico { acyclic[framePaiParaFrameFilho, Frame] }
/* ******************************** */
run { } for 10 but 5 int 

/* ************************************ */
/*Instância*/
one sig PerformSessionSSD,PerformTransactionSSD extends SystemSequenceDiagram {}    
one sig Customer,ATMSystem extends Lifeline {}    
one sig Loop1 extends Loop {}    
one sig Opt1 extends Opt {}    
one sig Break1 extends Break {}    
one sig CardNotOK,OKIsTrue,CustomerWantsMore extends Condition {}    
one sig Operand1,Operand2,Operand3 extends Operand {}    
one sig insertCard,isCardOK,readCard,requestPin,enterPin,requestTransaction,wantAnotherTransaction,selectNo,
        ejectCard,terminateSession,ejectCard2,notify,selectYes extends Message {}
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
            Operand <: messages = Operand1 -> 0 -> ejectCard2 +
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
             ejectCard2 -> ATMSystem +
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
             ejectCard2 -> ATMSystem +
             notify -> Customer +
             selectYes -> ATMSystem
}
