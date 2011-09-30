module textualUseCase

open util/relation as rel
open util/ternary as ter

/* Use Case Model */
abstract one sig UseCaseModel {
	/*rootUCName: one UCName,*/
	useCases: UCName -> UseCase,
    actors: some Actor,
    use: Actor set -> some UseCase,
}{
	/*rootUCName in dom[useCases]*/
    // para todos os pares (UCName, UseCase) na relação useCases, o UCName é o nome do UseCase associado
	all n: UCName, u: UseCase | n -> u in useCases => n in u.name
    // a use case can not be associated with two actors related with inheritsFrom
    all u: UCName.useCases, disj a, a': use.u | a not in a'.^(Actor<:inheritsFrom)
    // no heirs of an actor associated with a use case can be associated with a use case
    all a: actors | some use[a] => no use[ a.^(Actor<:inheritsFrom) ]
    // an actor cannot be associated with two use cases related with inheritsFrom 
    all a: actors, disj u, u': use[a] | u not in u'.^inheritsFrom
    // um actor só pode 'usar' UC's de nível USERGOAL
    all uc: use[Actor] | uc.goalLevel in USERGOAL
}
/* ************************************ */
/* Actores */
abstract sig Actor {
    inheritsFrom: lone Actor    
} {
    // todos os actores existentes pertencem ao UseCaseModel
    this in UseCaseModel.actors    
}
abstract sig User, ComputerSystem extends Actor {}

// a relação de herança entre actores é acíclica
fact  { acyclic[Actor<:inheritsFrom, Actor] }
// humanos e máquinas não herdam uns dos outros
fact { all u: User, s: ComputerSystem | u not in s.inheritsFrom and s not in u.inheritsFrom }
/* ************************************ */
/* Use Case */
abstract sig UseCase {
	name: one UCName,
    goalLevel: one GoalLevel,
	mainScenario: one Flow,
	alternatives: set Alternative,
    inheritsFrom: set UseCase
}{
	// o conj de alternativas de um UC é igual ao conj de
	// alternativas dos seus passos
	alternatives = { a: Alternative | 
		a.id in (mainScenario.flow.stepType[Int]).alternatives +
        (ActionBlock <: mainScenario.flow[Int]).actionSteps[Int].(stepType.alternatives)}
    // todos os UseCase têm de pertencer ao UseCaseModel
    this in UseCaseModel.useCases[UCName]
    // o mainScenario dos UC 'usados' pelo Actor,
    // é um BasicFlow ou um EmptyFlow (no caso do uc ser abstracto)
    this in UseCaseModel.use[Actor] => mainScenario in BasicFlow + EmptyFlow
    // os use cases utilizados pelo actores são do tipo USERGOAL
    this in UseCaseModel.use[Actor] => goalLevel in USERGOAL
    // os use cases de especialização têm o mesmo tipo do use case que especializam
    some inheritsFrom => goalLevel in inheritsFrom.@goalLevel
    // todos os UC têm de ser 'usados' por um Actor, extender um UC, ser íncluido por um UC, ou herdar de um UC
    this in UseCaseModel.use[Actor] + extende.UseCase + inclui[UseCase] + @inheritsFrom.UseCase
    // o mainScenario de um UC não pode ser o mesmo de uma das suas alternativas
    mainScenario not in alternatives.alternativeScenario
    // não existe herança múltipla entre UCs
    lone inheritsFrom
    // o fluxo de UCs abstractos é vazio (e o dos concretos não
    this in abstractUseCases => mainScenario in EmptyFlow /*else mainScenario not in EmptyFlow*/
    // UCs incluídos não podem ser 'usados' directamente (?)
    this in UseCase.inclui => this not in UseCaseModel.use[Actor]
    // UCs incluídos são do tipo SUBFUNCTION 
    this in UseCase.inclui => goalLevel in SUBFUNCTION
    // Fluxos de alternativa como AltHistory, ou UCException só podem ser caminho principal de UCs de extensão
    // (não podem ser AltPart)
    mainScenario in AltHistory + UCException => this in extende.UseCase
}

fact extensoesAciclicas { acyclic[extende, UseCase] and
                            all u,u':UseCase | u' in u.^inclui => u' not in u.extende }

enum GoalLevel { USERGOAL, SUBFUNCTION }
// inheritsFrom é assimétrico, irreflexivo e acíclico
fact { acyclic[UseCase <: inheritsFrom, UseCase]}
fact { bijective[name, UCName] }

/* ************************************ */
/* Fluxos */
abstract sig Flow { 
	flow: seq Step + ActionBlock
} { 
	// os passos Goto, Success, Failure, e Resume não podem pertence ao corpo de um UC, são apenas o último passo
	all s: Goto + Success + Failure + Resume | s not in Int.(butlast[flow])
	// para não haver flows soltos
	this in Alternative.alternativeScenario + UseCase.mainScenario
    // cada Flow está ligado, no máximo, a um mainScenario
    this not in EmptyFlow => lone this.~mainScenario 
    // se um Flow estiver ligado a um mainScenario e a algum alternativeScenario, isso significa que pertence
    // a um UseCase de extensão
    this in UseCase.mainScenario and this in Alternative.alternativeScenario => this.~alternativeScenario.type in EXTERNAL
} 
abstract sig AltFlow extends Flow {} {
	// os alt flows têm de ter pelo menos dois passos
	#flow > 1
}
abstract sig AltPart     extends AltFlow {} { last[flow] in Goto    }
abstract sig AltHistory  extends AltFlow {} { last[flow] in Success }
abstract sig UCException extends AltFlow {} { 
    last[flow] in Failure
    // a partir do momento em que se entra numa UCException, não é possível recuperar e entrar num fluxo que resulte em sucesso, ou seja,
    // alternativas com origem em UCException's, não podem ser do tipo AltHistory
    flow.stepType.alternatives.~id.alternativeScenario[Int] not in AltHistory and
        flow.actionSteps.stepType.alternatives.~id.alternativeScenario[Int][Int] not in AltHistory
}

abstract sig BasicFlow extends Flow {} {
    // os fluxos básicos de uc's de nivel USERGOAL terminam sempre em sucesso
    this.~mainScenario.goalLevel in USERGOAL => last[flow] in Success    
    // excepto o passo de Success, o corpo de BasicFlows é composto só por ActionBlocks e, eventualmente, passos Include
    Int.(butlast[flow]) in ActionBlock + Include
	// os basic flows têm de ter pelo menos dois passos
	#flow > 1
}

one sig EmptyFlow extends Flow{} {
    // este tipo de Flow só pode fazer parte de use cases abstractos
    this in abstractUseCases.mainScenario
	// os emtpy flows não contêm qualquer passo
	#flow = 0
}
abstract sig InsertionFlow extends Flow {} { 
    last[flow] in Resume
    // este tipo de fluxo apenas diz respeito a UCs de extensão ou inclusão
    this in extende.UseCase.mainScenario + UseCase.inclui.mainScenario
    #flow > 1
}
/* ************************************ */
/* Alternatives */
abstract sig Alternative {
	id: one AlternativeID,
	condition: one Condition,
	alternativeScenario: one AltFlow + InsertionFlow,
    type: one AlternativeType
} {
	// pra não haver alternatives soltos
	this in UseCase.alternatives
    // se a extensão for externa então o AltFlow está contido noutro UC
    type in EXTERNAL => alternativeScenario in UseCase.mainScenario
    // se a alternativa corresponder a um UC de extensão, o seu fluxo só pode ser um AltHistory, UCException, ou InsertionFlow.
    // de modo a evitar Goto's perigosos, ou seja, que apontem para passos de outros UC
    type in EXTERNAL => alternativeScenario in AltHistory+UCException+InsertionFlow
    // as alternativas correspondentes a passos do tipo UserDecision são iniciadas por um passo do tipo Input
    (some c : id.~alternatives | c in UserDecision) => first[alternativeScenario.flow].stepType in Input
    // as alternativas correspondentes a passos do tipo SystemValidation são iniciadas por um passo do tipo SystemR ou Output
    (some c : id.~alternatives | c in SystemValidation) => first[alternativeScenario.flow].stepType in SystemR + Output
}
enum AlternativeType { INTERNAL, EXTERNAL }

// cada alternativa tem a sua condição e o seu fluxo
fact { all disj a,a': Alternative | a.condition not in a'.condition && a.alternativeScenario not in a'.alternativeScenario }
fact { bijective[id, AlternativeID] } 
											  
abstract sig Condition{}{
    this in Alternative.condition    
}
/* ************************************ */
/* Action Blocks */
abstract sig ActionBlock {
	actionSteps: seq Atom
} {
	// o ActionBlock mais pequeno possivel tem dois actionSteps (um query, input-output)
	#actionSteps > 1
	// o 1º passo dos AB é sempre um Input
	first[actionSteps].stepType in Input + UserDecision
	// e é so o 1º, nunca aparece no corpo restante de um AB
	Input not in Int.(rest[actionSteps]).stepType
	// o Output, se aparecer, é sempre na última posição de um AB
	/*Output not in Int.(butlast[actionSteps]).stepType*/
	// os actionsBlocks tem de estar ligados a Flow's
	some f: Flow | this in f.flow[Int]
    // cada AB só pode aparecer uma vez num Flow e apenas num único Flow
    lone flow.this
}

abstract sig Query extends ActionBlock {
} {
    // o último passo de um Query é um Output
	last[actionSteps].stepType in Output
	// os passos intermédios só podem ser Choice
	SystemR not in Int.actionSteps.stepType
}

abstract sig Internal extends ActionBlock {	
} {
    // os ActionBlock Internal não contêm passos Output
	Output not in Int.actionSteps.stepType
    // e contêm, obrigatoriamente, pelo menos um passo SystemResponsability
	some s: SystemR | s in Int.actionSteps.stepType
}

abstract sig Service extends ActionBlock {	
} {
    // o último passo de um Service é um Output
	last[actionSteps].stepType in Output
    // os ActionBlock Service não contêm passos do tipo Choice
	Choice not in Int.actionSteps.stepType
    // e contêm, também, pelo menos um passo SystemResponsability
	some s: SystemR | s in Int.actionSteps.stepType
}

abstract sig Validation extends ActionBlock {	
} {
    // os ActionBlock Validation contêm pelo menos um passo SystemValidation
	some v: SystemValidation | v in Int.actionSteps.stepType
    // não contêm nenhum SystemResponsability
	SystemR not in Int.actionSteps.stepType
    // nem nenhum Output
	Output not in Int.actionSteps.stepType
}

abstract sig Complete extends ActionBlock {	
} {
    // o último passo dos ActionBlock do tipo Complete é um Output
	last[actionSteps].stepType in Output
    // contêm obrigatoriamente algum passo SystemValidation ou SystemVerification
	some v: SystemValidation /*+ SystemVerification*/ | v in Int.actionSteps.stepType
    // e também algum passo SystemResponsability
	some s: SystemR | s in Int.actionSteps.stepType
}
/* ************************************ */
/* Kinds of Steps */
abstract sig Step{ stepID: one StepID } { 
    // para não haver Steps soltos
    this in Flow.flow[Int] + ActionBlock.actionSteps[Int]
    // um Step só pode aparecer uma vez num flow e apenas num único flow
    /*lone flow.this*/
}

fact { bijective[stepID, StepID] }

/* Atom */
abstract sig Atom extends Step{
	stepType: one ActionStep,
	/*label: one Label,*/
} {
    // cada Atom tem uma label diferente
    --no disj a,a': Atom | a.@label in a'.@label
    // cada Atom é mapeado uma única vez ou pela relação actionSteps ou pela relação flow
    one this.~(select13[actionSteps] + select13[flow])
}

abstract sig StepID{}
/*sig Label{}{ Label in Atom.label }*/
abstract sig AlternativeID{}
/* Goto */
abstract sig Goto extends Step{
	otherStepID: one StepID
} {
    // o StepID referenciado pelo otherStepID de cada Goto só pode pertencer a passos que estejam contidos no fluxo que a extensão à qual esse Goto 
    // pertence extende, ou seja, os Goto só podem apontar para o fluxo pai (mas nunca para outros Goto, Failure ou Success; não faz sentido).
   let flowDoPai = this.~(select13[flow]).~alternativeScenario.~alternatives.mainScenario.flow[Int] {
        otherStepID in (flowDoPai.@stepID + (flowDoPai.actionSteps[Int]).@stepID) - Goto.@stepID - Failure.@stepID - Success.@stepID
    }
}

/* Include */
abstract sig Include extends Step{
	ucName: one UCName
} {
    this in Int.(UseCase.alternatives.alternativeScenario.flow + UseCase.mainScenario.flow)    
}
fact { ran[ucName] in mid[useCases] } 
// não há inclusões cíclicas
fact { acyclic[inclui, UseCase] } 

abstract sig UCName{}
/* Success and Failure */
lone sig Success extends Step{ }
lone sig Failure extends Step{ }

lone sig Resume extends Step {} { this in InsertionFlow.flow[Int] }
/* ************************************ */
/* Action Steps */
abstract sig ActionStep {}
lone sig Input extends ActionStep {}
lone sig Output extends ActionStep {}
lone sig SystemR extends ActionStep {}
abstract sig Choice extends ActionStep {
    alternatives: some AlternativeID
} {
    // se um Choice pertencer a uma alternativa, o id da alternativa não pode estar contido
    // no conjunto de id's para o qual esse Choice aponta
    some a: Alternative | (this in a.alternativeScenario.flow.stepType[Int] or
                          this in a.alternativeScenario.flow.actionSteps.stepType[Int][Int])
                => a.id not in alternatives
    // os passos Choice são únicos, e não pode haver dois Atoms para um dado Choice (ao contrário dos outros ActionSteps)
    one this.~stepType
}
abstract sig UserDecision extends Choice {}
abstract sig SystemValidation extends Choice {}
/*one sig SystemVerification extends Choice {}*/
/* ************************************ */
/* Helper Functions */
fun inclui : UseCase -> UseCase { 
	{ uc1,uc2 : UseCase | uc2 in name.(uc1.mainScenario.flow.ucName[Int]) or
                          uc2 in name.(uc1.alternatives.alternativeScenario.flow.ucName[Int]) or
                          (some uc3: UseCase | uc3 in uc2.^inheritsFrom and uc3 in name.(uc1.mainScenario.flow.ucName[Int]) ) or
                          (some uc3: UseCase | uc3 in uc2.^inheritsFrom and uc3 in name.(uc1.alternatives.alternativeScenario.flow.ucName[Int]) )
    }
}
fun extende : UseCase -> UseCase {
    {  uc1,uc2 : UseCase | some a: uc2.alternatives | a.type in EXTERNAL and uc1.mainScenario in a.alternativeScenario }
}
fun parentsOf[a : Actor] : lone Actor {
    a.(Actor<:inheritsFrom)
}
fun childrenOf[a : Actor] : set Actor {
    (Actor<:inheritsFrom).a
}
pred isConnected [a : Actor] {
   some parentsOf[a] or some childrenOf[a]
}
fun useCasesAssociatedWith[a : Actor] : set UseCase {
    UseCaseModel.use[a]
}
fun abstractUseCases : set UseCase {
    { u : UseCase | u in UseCase.inheritsFrom }
}
/* ************************************ */
// Show
run { } for 6 but exactly 1 Actor, exactly 3 UseCase, exactly 1 BasicFlow, exactly 1 AltFlow, exactly 1 InsertionFlow

