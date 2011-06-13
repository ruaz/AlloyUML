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
	Frame in SystemSequenceDiagram.messages[univ]
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
	messages: seq Message
} {
	// não há operandos "soltos"
	Operand in Opt.operand + Break.operand + Loop.operand + Alt.operands[univ]
}
/* ******************************** */
/* Helper Functions */
fun referencia : SystemSequenceDiagram -> SystemSequenceDiagram {
	{ sd1,sd2 : SystemSequenceDiagram | sd2.seqDid in sd1.messages.reference[univ] }
}
/* ******************************** */
/* Helper Facts */
// se um DSS é referenciado por outro, então tem o mesmo actor e sistema que o que o referencia
fact { all sd1,sd2 : SystemSequenceDiagram | sd1 -> sd2 in referencia 
		=> sd2.actor in sd1.actor && sd2.system in sd1.system }
// o actor de um DSS não pode ser o sistema de outro e vice-versa
fact { all sd1,sd2 : SystemSequenceDiagram | sd1.actor not in sd2.system }
/* ******************************** */
run { #referencia = 1 } for 5 but exactly 2 SystemSequenceDiagram, exactly 1 Loop, exactly 1 Alt, exactly 1 Opt, exactly 1 Break, exactly 1 Ref, exactly 3 Message
