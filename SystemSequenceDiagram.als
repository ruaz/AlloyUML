module umlFormalModels/SystemSequenceDiagram

open util/relation
open util/ternary

/* System Sequence Diagram */
abstract sig SystemSequenceDiagram {
	seqDid: one SeqDid, 
	system: one System,
	actor: one Actor,
	messages: seq Message + Frame + Ref,
} {
    // actor e sistema são duas lifelines diferentes
	/*system not in actor */
    // as mensagens trocadas num dado SSD usam as mesmas lifelines que esse SSD
    /*(messages[Int].source + messages[Int].target) in (system + actor)*/
    // 
}
// relação de 1-1 entre SystemSequenceDiagram e seqDid
fact { bijective[seqDid, SeqDid] }
// não pode haver referências cíclicas
fact { acyclic[referencia, SystemSequenceDiagram] } 

abstract sig SeqDid {}
/* ******************************** */
/* Actor */
one sig Actor {}
one sig System {}
/* Lifeline */
/*abstract sig Lifeline {} { */
/*	// não há lifelines "soltas", ou são o actor ou o sistema*/
/*	this in SystemSequenceDiagram.system + SystemSequenceDiagram.actor*/
/*}*/
/* ******************************** */
/* Frame */
abstract sig Frame {} {
    // todos os frames pertencem ao conjunto de mensagens de um SSD ou de um operando
	this in SystemSequenceDiagram.messages[Int] + Operand.messages[Int]
}

/* Alt */
abstract sig Alt extends Frame {
	conditions: seq Condition, 
	operands: seq Operand
} {
	#conditions = #operands
	#conditions > 1
}

/* Opt */
abstract sig Opt extends Frame  {
	condition: one Condition,
	operand: one Operand
}

/* Break */
abstract sig Break extends Frame  {
	condition: one Condition,
	operand: one Operand
}

/* Loop */
abstract sig Loop extends Frame  {
	condition: one Condition,
	operand: one Operand,
	minint: one Int,
	maxint: one Int
} {
	minint <= maxint
	minint > 0
}

/* Operand */
abstract sig Operand {
	messages: seq Message + Frame + Ref
} {
	// não há operandos "soltos"
	this in Opt.operand + Break.operand + Loop.operand + Alt.operands[Int]
}
abstract sig Condition {} {
    this in Opt.condition + Loop.condition + Break.condition + Alt.conditions[Int]
}
/* ******************************** */
/* Ref */
abstract sig Ref {
	reference: one SeqDid
} {
	// não há Refs "soltos"
	this in SystemSequenceDiagram.messages[Int] + Operand.messages[Int]
}

/* ******************************** */
/* Message */
abstract sig Message {
	source: one Actor + System,
	target: one Actor + System
} {
	// não há mensagens "soltas"
	this in SystemSequenceDiagram.messages[Int] + Operand.messages[Int]
}
/* ******************************** */
/* Helper Functions */
// devolve pares de SSD's (A,B) em que A referencia B
fun referencia : SystemSequenceDiagram -> SystemSequenceDiagram {
	{ sd1,sd2 : SystemSequenceDiagram | sd2.seqDid in sd1.messages.reference[Int] }
}
// devolve pares de frames (A,B) em que A contém B
fun framePaiParaFrameFilho : Frame -> Frame {
    { frameP,frameF: Frame | frameF in (frameP.(Opt <: operand).messages[Int] +
                                        frameP.(Break <: operand).messages[Int] +
                                        frameP.(Loop <: operand).messages[Int] +
                                        frameP.operands[Int].messages[Int])}
}
/* ******************************** */
/* Helper Facts */
// se um DSS é referenciado por outro, então tem o mesmo actor e sistema que o SSD que o referencia
fact { all sd1,sd2 : SystemSequenceDiagram | sd1 -> sd2 in referencia 
		=> sd2.actor in sd1.actor && sd2.system in sd1.system }
// o actor de um DSS não pode ser o sistema de outro e vice-versa
/*fact { all sd1,sd2 : SystemSequenceDiagram | sd1.actor not in sd2.system }*/
// não é possível encontrar um frame dentro de si próprio
fact framesPaiFilhoAciclico { acyclic[framePaiParaFrameFilho, Frame] }
/* ******************************** */
run { } for 10 but 5 int 
