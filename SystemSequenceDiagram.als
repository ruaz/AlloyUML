module umlFormalModels/SystemSequenceDiagram

open util/boolean
open util/relation

/* System Sequence Diagram */
abstract sig SystemSequenceDiagram {
	seqDid: SeqDid, 
	system: Lifeline,
	actor: Lifeline,
	messages: seq Message + Frame + Ref
} {
	system not in actor // actor e sistema são duas lifelines diferentes
	#messages > 0 // não permite DS vazios
	lone messages.conditions.True[univ]
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
	Ref in SystemSequenceDiagram.messages[univ]
}

/* ******************************** */
/* Frame */
abstract sig Frame {} {
	Frame in SystemSequenceDiagram.messages[univ] + Operand.messages[univ]
}

/* Alt */
abstract sig Alt extends Frame {
	conditions: seq Bool, // não sei se Bool será a melhor representação
						  // das condições
	operands: seq Operand
} {
	#conditions = #operands
	#conditions > 0
}

/* Opt */
abstract sig Opt extends Frame  {
	condition: Bool,
	operand: Operand
}

/* Break */
abstract sig Break extends Frame  {
	condition: Bool,
	operand: Operand
}

/* Loop */
abstract sig Loop extends Frame  {
	condition: Bool,
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
// o actor de um DSS não pode ser o sistema de outro e vice-versa
fact { all sd1,sd2 : SystemSequenceDiagram | sd1.actor not in sd2.system }
// não é possível encontrar um frame dentro de si próprio
fact framesPaiFilhoAciclico { acyclic[framePaiParaFrameFilho, Frame] }
/* ******************************** */
/* Instância para teste */
/*one sig SystemSequenceDiagram1 extends SystemSequenceDiagram {}*/
/*one sig System extends Lifeline {}*/
/*one sig Actor extends Lifeline {}*/
/*one sig SeqDid1 extends SeqDid {}*/
/*one sig Message1,Message2,Message3,Message4,Message5,Message6,Message7,Message8,Message9,Message10,Message11,Message12,Message13 extends Message {}*/
/*one sig Opt1, Opt2 extends Opt {}*/
/*one sig Break1, Break2 extends Break {}*/
/*one sig Loop1, Loop2 extends Loop {}*/
/*one sig Operand1, Operand2, Operand3, Operand4, Operand5, Operand6 extends Operand {}*/
/*/* ************************************ */
/*fact ssds { */
/*    seqDid = SystemSequenceDiagram1 -> SeqDid1*/
/*    system = SystemSequenceDiagram1 -> System*/
/*    actor = SystemSequenceDiagram1 -> Actor*/
/*    SystemSequenceDiagram1 <: messages = SystemSequenceDiagram1 -> 0 -> Loop1 +*/
/*               SystemSequenceDiagram1 -> 1 -> Message4 +*/
/*               SystemSequenceDiagram1 -> 2 -> Message5 +*/
/*               SystemSequenceDiagram1 -> 3 -> Break1 +*/
/*               SystemSequenceDiagram1 -> 4 -> Message7 +*/
/*               SystemSequenceDiagram1 -> 5 -> Break2 +*/
/*               SystemSequenceDiagram1 -> 6 -> Loop2 +*/
/*               SystemSequenceDiagram1 -> 7 -> Message12 +*/
/*               SystemSequenceDiagram1 -> 8 -> Message13*/
/*}*/
/*fact Messages {*/
/*    source = Message1 -> Actor +*/
/*             Message2 -> System +*/
/*             Message3 -> Actor +*/
/*             Message4 -> Actor +*/
/*             Message5 -> System +*/
/*             Message6 -> System +*/
/*             Message7 -> System +*/
/*             Message8 -> Actor +*/
/*             Message9 -> Actor +*/
/*             Message10 -> System +*/
/*             Message11 -> System +*/
/*             Message12 -> System +*/
/*             Message13 -> System*/
/**/
/*    target = Message1 -> System +*/
/*             Message2 -> Actor +*/
/*             Message3 -> System +*/
/*             Message4 -> System +*/
/*             Message5 -> System +*/
/*             Message6 -> Actor +*/
/*             Message7 -> Actor +*/
/*             Message8 -> System +*/
/*             Message9 -> System +*/
/*             Message10 -> System +*/
/*             Message11 -> Actor +*/
/*             Message12 -> System +*/
/*             Message13 -> Actor*/
/*}*/
/*fact Opts {*/
/*    Opt <: condition = Opt1 -> True + Opt2 -> True*/
/*    Opt <: operand = Opt1 -> Operand2 +*/
/*                     Opt2 -> Operand6*/
/*}*/
/*fact Breaks {  */
/*    Break <: condition = Break1 -> True + Break2 -> True*/
/*    Break <: operand = Break1 -> Operand3 +*/
/*                       Break2 -> Operand4*/
/*}*/
/*fact Loops {  */
/*    Loop <: condition = Loop1 -> True + Loop2 -> True*/
/*    Loop <: operand = Loop1 -> Operand1 +*/
/*                      Loop2 -> Operand5*/
/*    // valores aleatorios no min e maxint*/
/*    minint = Loop1 -> 1 + Loop2 -> 1*/
/*    maxint = Loop1 -> 1 + Loop2 -> 1*/
/*}*/
/*fact Operands {  */
/*    Operand <: messages = Operand1 -> 0 -> Message1 +*/
/*               Operand1 -> 1 -> Message2 +*/
/*               Operand1 -> 2 -> Opt1 +*/
/*               Operand2 -> 0 -> Message3 +*/
/*               Operand3 -> 0 -> Message6 +*/
/*               Operand4 -> 0 -> Message8 +*/
/*               Operand5 -> 0 -> Message9 +*/
/*               Operand5 -> 1 -> Message10 +*/
/*               Operand5 -> 2 -> Opt2 +*/
/*               Operand6 -> 0 -> Message11*/
/*}*/
/**/
run { } for 10 but 5 int 
