module textualUseCase

/*
* Adaptado de 'LTS Semantics for Use Case Models', por Daniel Sinnig
*/

open util/relation as rel
open util/ternary as ter

// Fig. 1
/* Goal Level Properties */
/*abstract sig GoalLvlProp{}*/
/*sig Summary extends GoalLvlProp{}*/
/*sig UserGoal extends GoalLvlProp{}*/
/*sig SubFunction extends GoalLvlProp{}*/
/* ************************************ */
/* Step Types */
/*abstract sig StepType{}*/
/*sig System extends StepType{}*/
/*sig Interaction extends StepType{}*/
/*sig Internal extends StepType{}*/
abstract sig ActionStep {}
sig Input extends ActionStep {}
sig Output extends ActionStep {}
sig SystemR extends ActionStep {}
/*abstract sig Assume extends ActionStep {}*/
abstract sig Choice extends ActionStep {
    extensions: some ExtensionID
} {
    extensions not in this.~stepType.~(select13[actionSteps]).~(select13[flow]).~extensionScenario.id 
}
sig UserChoice extends Choice {}
sig SystemCheck extends Choice {}
/* ************************************ */
/* Use Case Properties */
/*sig UCProperties{*/
	/*goal: one GoalProperty,*/
	/*primaryActor: one ActorProperty,*/
	/*goalLevel: one GoalLvlProp,*/
	/*precondition: one PrecondProperty*/
/*}*/
//fact { bijective[goalLevel, GoalLvlProp] }

/*sig GoalProperty{}*/
/*sig ActorProperty{}*/
/*sig PrecondProperty{}*/
abstract sig Actor {
    inheritsFrom: lone Actor    
} {
    this in UseCaseModel.actors    
}
// a relação de herança entre actores é acíclica
fact  { acyclic[Actor<:inheritsFrom, Actor] }
abstract sig User, ComputerSystem extends Actor {}
// humanos e máquinas não herdam uns dos outros
/*fact { all u: User, s: ComputerSystem | u not in s.inheritsFrom and s not in u.inheritsFrom }*/
/* ************************************ */
/* Kinds of Steps */
abstract sig Step{ stepID: one StepID } { 
    // para não haver Steps soltos
    this in /*Choice.alternatives[univ] + (retirados os passos Choice)*/
            /*Concurrent.steps +*/
            Flow.flow[univ] + ActionBlock.actionSteps[univ]
    // um Step só pode aparecer uma vez num flow e apenas num único flow
    lone flow.this
}
fact { bijective[stepID, StepID] } //Def. 1.1 os id's são únicos. Def. 1.2 não há StepID's sem um Step
/* Atom */
abstract sig Atom extends Step{
	stepType: one ActionStep,
	label: one Label,
	/*extensions: set ExtensionID*/
} {
	/*stepType not in Assume => #extensions = 0*/
    // cada Atom tem uma label diferente
    --no disj a,a': Atom | a.@label in a'.@label
    // se um Atom pertence a um Flow então não pertence a nenhum actionSteps de AB's (e vice-versa)
    this in Flow.flow[univ] => this not in ActionBlock.actionSteps[univ]
}
fact { bijective[stepType,ActionStep] }

abstract sig StepID{}
sig Label{}{ Label in Atom.label }
abstract sig ExtensionID{}
/* Choice */
/*abstract sig Choice extends Step{*/
/*	alternatives: set (seq Step),*/
/*	extensions: set ExtensionID*/
/*}*/
/* Concurrent */
/*abstract sig Concurrent extends Step{*/
/*	steps: set (set Step),*/
/*	extensions: set ExtensionID*/
/*}*/
/* Goto */
abstract sig Goto extends Step{
	otherStepID: one StepID
} {
    // o StepID referenciado pelo otherStepID de cada Goto só pode pertencer a passos que estejam contidos no fluxo que a extensão à qual esse Goto 
    // pertence extende, ou seja, os Goto só podem apontar para o fluxo pai (mas nunca para outros Goto, Failure ou Success; não faz sentido).
   /*let passosDoPai = this.~(select13[flow]).~extensionScenario.~extensions.mainScenario.flow.actionSteps[univ][univ] {*/
    /*    otherStepID in passosDoPai.@stepID - Goto.@stepID - Failure.@stepID - Success.@stepID*/
    /*}*/
}
fact gotoNaoCiclicos { Goto.otherStepID & Goto.stepID = none }
/* Include */
abstract sig Include extends Step{
	ucName: one UCName
} {
    Include in univ.(UseCase.extensions.extensionScenario.flow + UseCase.mainScenario.flow)    
}
fact { ran[ucName] in mid[useCases] } //Def. 1.3 a)
fact { acyclic[inclui, UseCase] } // Def. 1.3 não há inclusoes ciclicas 
abstract sig UCName{}
/* Success and Failure */
abstract sig Success extends Step{ }
abstract sig Failure extends Step{ }
/* ************************************ */
/* Extensions */
abstract sig Extension {
	id: ExtensionID,
	condition: one Condition,
	extensionScenario: AltFlow,
    type: one ExtensionType
} {
	// pra não haver extensions soltos
	Extension in univ.extensions
    // se a extensão for externa então o AltFlow está contido noutro UC
    type in EXTERNAL => extensionScenario in UseCase.mainScenario
}
enum ExtensionType { INTERNAL, EXTERNAL }


// cada extensão tem a sua condição e o seu altFlow
fact { all disj e,e': Extension | e.condition not in e'.condition && e.extensionScenario not in e'.extensionScenario }
fact { bijective[id, ExtensionID] } // Def. 1.1 os id's são únicos. 
											   //Def. 1.2 não há ExtensionID's sem um Extension
abstract sig Condition{}{
    Condition in Extension.condition    
}
/* ************************************ */
/* Use Case */
abstract sig UseCase {
	name: UCName,
	/*properties: one UCProperties,*/
    goalLevel: one GoalLevel,
	mainScenario: one Flow,
	extensions: set Extension,
    inheritsFrom: set UseCase
}{
	// o conj de extensions (alt flows) de um UC é igual ao conj de
	// extension dos seus passos
	extensions = { e: Extension | 
		e.id in (mainScenario.flow.stepType[univ]).extensions +
        (ActionBlock <: mainScenario.flow[univ]).actionSteps[univ].(stepType.extensions)}
    // todos os UseCase têm de pertencer a algum UseCaseModel
    UseCase in UseCaseModel.useCases[univ]
    // se o UC for USERGOAL, o mainScenario é um BasicFlow, senão é um AltFlow
    /*goalLevel in USERGOAL => mainScenario in BasicFlow else mainScenario in AltFlow*/
    // todos os UC têm de ser 'usados' por um Actor, extender um UC, ser íncluido por um UC, ou herdar de um UC
    this in UseCaseModel.use[Actor] + extende.UseCase + inclui[UseCase] + @inheritsFrom.UseCase
    // o mainScenario de um UC não pode ser o mesmo de uma das suas extensões
    mainScenario not in extensions.extensionScenario
}

fact extensoesAciclicas { acyclic[extende, UseCase] and
                            all u,u':UseCase | u' in u.^inclui => u' not in u.extende }

enum GoalLevel { USERGOAL, SUBFUNCTION }
// inheritsFrom é assimétrico, irrflexivo e aciclico
fact { acyclic[UseCase <: inheritsFrom, UseCase]}
fact { bijective[name, UCName] }

/* ************************************ */
/* Use Case Model (Def.1) */
abstract sig UseCaseModel {
	rootUCName: one UCName,
	useCases: UCName -> UseCase,
    actors: some Actor,
    use: Actor set -> some UseCase,
}{
	rootUCName in dom[useCases]
	all n: UCName, u: UseCase | n -> u in useCases => n in u.name
    // a use case can not be associated with two actors related with inheritsFrom
    all u: UCName.useCases, disj a, a': use.u | a not in a'.^(Actor<:inheritsFrom)
    // no heirs of an actor associated with a use case can be associated with a use case
    all a: actors | some use[a] => no use[ a.^(Actor<:inheritsFrom) ]
    // an actor cannot be associated with two use cases related with inheritsFrom 
    all a: actors, disj u, u': use[a] | u not in u'.^inheritsFrom
    // um actor só pode 'usar' UC's de nível USERGOAL
    all uc: use[univ] | uc.goalLevel in USERGOAL
}

/* ************************************ */
abstract sig ActionBlock {
	actionSteps: seq Atom
} {
	// os action blocks não podem estar vazios
	#actionSteps > 0
	// o 1º passo dos AB é sempre um Input
	this not in DecisionBlock => first[actionSteps].stepType in Input
	// e é so o 1º, nunca aparece no corpo restante de um AB
	Input not in univ.(rest[actionSteps]).stepType
	// o Output, se aparecer, é sempre na última posição de um AB
	Output not in univ.(butlast[actionSteps]).stepType
	// os actionsBlocks tem de estar ligados a Flow's
	all ab: ActionBlock | some f: Flow | ab in f.flow[univ]
    // cada AB só pode aparecer uma vez num Flow e apenas num único Flow
    lone flow.this
}

abstract sig Query extends ActionBlock {
	
} {
	last[actionSteps].stepType in Output
	// os passos intermédios só podem ser Assume's
	SystemR not in univ.actionSteps.stepType
}

abstract sig Internal extends ActionBlock {
	
} {
	Output not in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}

abstract sig Service extends ActionBlock {
	
} {
	last[actionSteps].stepType in Output
	Choice not in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}

abstract sig Validation extends ActionBlock {
	
} {
	some c: SystemCheck | c in univ.actionSteps.stepType
	SystemR not in univ.actionSteps.stepType
	Output not in univ.actionSteps.stepType
}

abstract sig Complete extends ActionBlock {
	
} {
	last[actionSteps].stepType in Output
	some c: Choice | c in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}

abstract sig DecisionBlock extends ActionBlock {} {
    // em todos os DecisionBlock há um passo Choice; e é o único passo.
    one c: Choice | c in actionSteps.stepType[univ] && #actionSteps = 1
}

/* ************************************ */
/* Helper Signatures */
abstract sig Flow { 
	flow: seq Step + ActionBlock
} { 
	// os passos Goto, Success e Failure não podem pertence ao corpo de um UC, são apenas o último passo
	all s: Goto + Success + Failure | s not in univ.(butlast[flow])
	// pra n haver flows soltos
	Flow in Extension.extensionScenario + UseCase.mainScenario
	// os flows têm de ter pelo menos dois passos (discutivel)
	#flow > 1
    // cada Flow está ligado, no máximo, a um mainScenario
    lone this.~mainScenario
} 
abstract sig AltFlow extends Flow {} {}
abstract sig AltPart     extends AltFlow {} { last[flow] in Goto    }
abstract sig AltHistory  extends AltFlow {} { last[flow] in Success }
abstract sig UCException extends AltFlow {} { last[flow] in Failure }

abstract sig BasicFlow extends Flow {} {
    // os fluxos básicos de uc's de nivel USERGOAL terminam sempre em sucesso
    /*this.~mainScenario.goalLevel in USERGOAL => last[flow] in Success    */
    // excepto o passo de Success, o corpo de basic flows é composto so por AB's
    /*Int.(butlast[flow]) in ActionBlock*/
}
/*fact { all s:Step | s in univ.(univ.flow) } //para não haver Step's fora de Flows*/
/* ************************************ */
/* Helper Functions */
fun inclui : UseCase -> UseCase { 
	{ uc1,uc2 : UseCase | uc2 in name.(uc1.mainScenario.flow.ucName[univ]) }
}
fun extende : UseCase -> UseCase {
    {  uc1,uc2 : UseCase | some e: uc2.extensions | e.type in EXTERNAL and uc1.mainScenario in e.extensionScenario }
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
/* ************************************ */
// Show
run { } for 10

// Entities
one sig ATMUseCaseModel extends UseCaseModel {}    
/* ************************************ */
one sig Customer extends User {}    
/* ************************************ */
one sig PerformSession, PerformTransaction, HandleInvalidPIN, WithdrawMoney, TransferMoney extends UseCase {}    
/* ************************************ */
one sig Ext1,Ext2,Ext3,Ext4,Ext5 extends Extension {}    
/* ************************************ */
one sig Flow1,Flow2,Flow3,Flow4 extends BasicFlow {}
one sig Exception1,Exception2 extends UCException {}
one sig AltPart1,AltPart2,AltPart3 extends AltPart {}    
/* ************************************ */
one sig SystemCantReadCard,CustomerWantsMoreOps,TransactionNotApprovedDueToInvalidPIN,ThirdFailedPinAttempt,NotEnoughMoneyOnHand extends Condition {}
/* ************************************ */
one sig Complete1 extends Complete {}    
one sig Query1,Query2,Query3,Query4,Query5 extends Query {}    
one sig DecisionBlock1 extends DecisionBlock {}    
one sig Internal1,Internal2,Internal3,Internal4 extends Internal {}    
/* ************************************ */
/*PerformSession*/
one sig CustomerInsertsCard,SystemVerifiesCard,SystemReadsCard,SystemAsksPIN,
    CustomerEntersPIN, SystemRequestsOperation, SystemAsksForMoreOps,
    CustomerWantsNoMoreOps,CustomerEntersNo, SystemEjectsCard, SystemTerminatesSession extends Atom {}    
one sig IncludePerformTransaction extends Include {}    
one sig Success1 extends Success {}    
/*2a.Exception*/
one sig SystemEjectsCard2,SystemNotifiesCustomer extends Atom {}    
one sig Failure1 extends Failure {}    
/*9a.AltPart*/
one sig CustomerEntersYes extends Atom {}    
one sig Goto6 extends Goto {}    
/*ActionSteps*/
one sig Input1,Input2,Input3,Input4 extends Input {}
one sig Output1,Output2,Output3,Output4 extends Output {}
one sig SR1,SR2,SR3,SR4 extends SystemR {}
one sig SC1 extends SystemCheck {}
one sig UC1 extends UserChoice {}
/*StepIDs and ExtensionIDs*/
one sig Sid1,Sid2,Sid3,Sid4,Sid5,Sid6,Sid7,Sid8,Sid9,Sid10,Sid11,Sid12
			,Sid13,Sid14,Sid15,Sid16,Sid17,Sid18 extends StepID {}    
one sig Eid1,Eid2 extends ExtensionID {}    
/*UC Name*/
one sig Name1 extends UCName {}    
/* ************************************ */
/*PerformTransaction*/
one sig CustomerSelectsTransaction,SystemRequestsDetails,CustomerEntersDetails,SystemApprovesTransaction,SystemPerformsAdequateSteps,
        SystemPrintsReceipt extends Atom {}
/*ActionSteps*/
one sig Input5,Input6 extends Input {}    
one sig Output5 extends Output {}    
one sig SR5,SR6 extends SystemR {}    
one sig SC2 extends SystemCheck {}    
/*StepIDs and ExtensionIDs*/
one sig Sid19,Sid20,Sid21,Sid22,Sid23,Sid24 extends StepID {}    
one sig Eid3 extends ExtensionID {}    
/*UC Name*/
one sig Name2 extends UCName {}    
/* ************************************ */
/*HandleInvalidPIN*/
one sig SystemChecksFailedPINAttempts extends Atom {}    
one sig Goto4 extends Goto {}    
/*1a.Exception*/
one sig SystemRetainsCard,SystemNotifiesCustomer2 extends Atom {}    
one sig Failure2 extends Failure {}    
/*ActionSteps*/
one sig SC3 extends SystemCheck {}    
one sig SR7 extends SystemR {}    
one sig Output6 extends Output {}    
/*stepIDs and ExtensionIDs*/
one sig Sid25,Sid26,Sid27,Sid28,Sid29 extends StepID {}    
one sig Eid4 extends ExtensionID {}    
/*UC Name*/
one sig Name3 extends UCName {}    
/* ************************************ */
/*WithdrawMoney*/
one sig CustomerSelectsWithdraw,SystemRequestsAccType,CustomerSelectsAccType,SystemRequestsAmount,CustomerEntersAmount,SystemChecksMoneyOnHand,
        SystemApprovesTransaction2,SystemDispensesCash,SystemPrintsReceipt2 extends Atom {}    
/*5a.AltPart*/
one sig SystemNotifiesMoneyNA,SystemRequestsSmallerAmount extends Atom {}    
one sig GotoW4 extends Goto {}    
/*ActionSteps*/
one sig Input7,Input8,Input9 extends Input {}    
one sig Output7,Output8,Output9,Output10 extends Output {}    
one sig SC4,SC5 extends SystemCheck {}    
one sig SR8,SR9 extends SystemR {}    
/*stepIDs and ExtensionIDs*/
one sig Sid30,Sid31,Sid32,Sid33,Sid34,Sid35,Sid36,Sid37,Sid38,Sid39,Sid40,Sid41 extends StepID {}    
one sig Eid5 extends ExtensionID {}    
/*UC Name*/
one sig Name4 extends UCName {}    
/* ************************************ */
/*TransferMoney*/
one sig CustomerSelectsTransfer,SystemRequestsAccsAndAmount,CustomerEntersAccsAndAmount,SystemApprovesTransaction3,
        SystemPrintsReceipt3 extends Atom {}    
/*ActionSteps*/
one sig Input10,Input11 extends Input {}    
one sig Output11 extends Output {}    
one sig SC6 extends SystemCheck {}    
one sig SR10 extends SystemR {}    
/*stepIDs*/
one sig Sid42,Sid43,Sid44,Sid45,Sid46 extends StepID {}
/*UC Name*/
one sig Name5 extends UCName {}    
/* ************************************ */
fact ucmodel { actors = ATMUseCaseModel -> Customer
               use = ATMUseCaseModel -> Customer -> PerformSession
               useCases = ATMUseCaseModel -> Name1 -> PerformSession + ATMUseCaseModel -> Name2 -> PerformTransaction +
                         ATMUseCaseModel -> Name3 -> HandleInvalidPIN + ATMUseCaseModel -> Name4 -> WithdrawMoney +
                         ATMUseCaseModel -> Name5 -> TransferMoney }
fact usecases { goalLevel = PerformSession -> USERGOAL + PerformTransaction -> SUBFUNCTION + HandleInvalidPIN -> SUBFUNCTION + 
                    WithdrawMoney -> SUBFUNCTION + TransferMoney -> SUBFUNCTION
                extensions = PerformSession -> Ext1 + PerformSession -> Ext2 + PerformTransaction -> Ext3 + HandleInvalidPIN -> Ext4 + 
                    WithdrawMoney -> Ext5 + WithdrawMoney -> Ext3 + TransferMoney -> Ext3
                name = PerformSession -> Name1 + PerformTransaction -> Name2 + HandleInvalidPIN -> Name3 + WithdrawMoney -> Name4 +
                    TransferMoney -> Name5
                mainScenario = PerformSession -> Flow1 + PerformTransaction -> Flow2 + HandleInvalidPIN -> AltPart2 + WithdrawMoney -> Flow3 + 
                    TransferMoney -> Flow4
                inheritsFrom = WithdrawMoney -> PerformTransaction + TransferMoney -> PerformTransaction}
fact extensions { condition = Ext1 -> SystemCantReadCard + Ext2 -> CustomerWantsMoreOps + Ext3 -> TransactionNotApprovedDueToInvalidPIN + 
                    Ext4 -> ThirdFailedPinAttempt + Ext5 -> NotEnoughMoneyOnHand
                  type = Ext1 -> INTERNAL + Ext2 -> INTERNAL + Ext3 -> EXTERNAL + Ext4 -> INTERNAL + Ext5 -> INTERNAL
                  extensionScenario = Ext1 -> Exception1 + Ext2 -> AltPart1 + Ext3 -> AltPart2 + Ext4 -> Exception2 +
                      Ext5 -> AltPart3
                  id = Ext1 -> Eid1 + Ext2 -> Eid2 + Ext3 -> Eid3 + Ext4 -> Eid4 + Ext5 -> Eid5 }
fact flows { flow =
                    /*basic flows*/
                    Flow1 -> 0 -> Complete1 + 
                    Flow1 -> 1 -> Query1 + 
                    Flow1 -> 2 -> IncludePerformTransaction +
                    Flow1 -> 3 -> SystemAsksForMoreOps +
                    Flow1 -> 4 -> DecisionBlock1 +
                    Flow1 -> 5 -> Internal1 +
                    Flow1 -> 6 -> Success +

                    Flow2 -> 0 -> Query2 +
                    Flow2 -> 1 -> Internal2 +

                    Flow3 -> 0 -> Query3 +
                    Flow3 -> 1 -> Query4 +
                    Flow3 -> 2 -> Internal3 +

                    Flow4 -> 0 -> Query5 +
                    Flow4 -> 1 -> Internal4 +

                    /*alt flows*/
                    Exception1 -> 0 -> SystemEjectsCard2 +
                    Exception1 -> 1 -> SystemNotifiesCustomer +
                    Exception1 -> 2 -> Failure1 +
                    AltPart1 -> 0 -> CustomerEntersYes +
                    AltPart1 -> 1 -> Goto6 +

                    AltPart2 -> 0 -> SystemChecksFailedPINAttempts +
                    AltPart2 -> 1 -> Goto4 +
                    Exception2 -> 0 -> SystemRetainsCard +
                    Exception2 -> 1 -> SystemNotifiesCustomer2 +
                    Exception2 -> 2 -> Failure2 +

                    AltPart3 -> 0 -> SystemNotifiesMoneyNA +
                    AltPart3 -> 1 -> SystemRequestsSmallerAmount +
                    AltPart3 -> 2 -> GotoW4
}
fact actionBlocks { actionSteps = Complete1 -> 0 -> CustomerInsertsCard + 
                    Complete1 -> 1 -> SystemVerifiesCard +
                    Complete1 -> 2 -> SystemReadsCard +
                    Complete1 -> 3 -> SystemAsksPIN +
                    Query1 -> 0 -> CustomerEntersPIN +
                    Query1 -> 1 -> SystemRequestsOperation +
                    DecisionBlock1 -> 0 -> CustomerWantsNoMoreOps +
                    Internal1 -> 0 -> CustomerEntersNo +
                    Internal1 -> 1 -> SystemEjectsCard +
                    Internal1 -> 2 -> SystemTerminatesSession +

                    Query2 -> 0 -> CustomerSelectsTransaction +
                    Query2 -> 1 -> SystemRequestsDetails +
                    Internal2 -> 0 -> CustomerEntersDetails +
                    Internal2 -> 1 -> SystemApprovesTransaction +
                    Internal2 -> 2 -> SystemPerformsAdequateSteps +
                    Internal2 -> 3 -> SystemPrintsReceipt +

                    Query3 -> 0 -> CustomerSelectsWithdraw +
                    Query3 -> 1 -> SystemRequestsAccType +
                    Query4 -> 0 -> CustomerSelectsAccType +
                    Query4 -> 1 -> SystemRequestsAmount +
                    Internal3 -> 0 -> CustomerEntersAmount +
                    Internal3 -> 1 -> SystemChecksMoneyOnHand +
                    Internal3 -> 2 -> SystemApprovesTransaction2 +
                    Internal3 -> 3 -> SystemDispensesCash +
                    Internal3 -> 4 -> SystemPrintsReceipt2 +

                    Query5 -> 0 -> CustomerSelectsTransfer +
                    Query5 -> 1 -> SystemRequestsAccsAndAmount +
                    Internal4 -> 0 -> CustomerEntersAccsAndAmount +
                    Internal4 -> 1 -> SystemApprovesTransaction3 +
                    Internal4 -> 2 -> SystemPrintsReceipt3 
}
fact atoms { stepType = CustomerInsertsCard -> Input1 +
               SystemVerifiesCard -> SC1 +
               SystemReadsCard -> SR1 +
               SystemAsksPIN -> Output1 +
               CustomerEntersPIN -> Input2 +
               SystemRequestsOperation -> Output2 +
               SystemAsksForMoreOps -> Output3 +
               CustomerWantsNoMoreOps -> UserChoice +
               CustomerEntersNo -> Input3 +
               SystemEjectsCard -> SR2 +
               SystemTerminatesSession -> SR3 +

               SystemEjectsCard2 -> SR4 +
               SystemNotifiesCustomer -> Output4 +

               CustomerEntersYes -> Input4 +

               CustomerSelectsTransaction -> Input5 +
               SystemRequestsDetails -> Output5 +
               CustomerEntersDetails -> Input6 +
               SystemApprovesTransaction -> SC2 +
               SystemPerformsAdequateSteps -> SR5 +
               SystemPrintsReceipt -> SR6 +

               SystemChecksFailedPINAttempts -> SC3 +

               SystemRetainsCard -> SR7 +
               SystemNotifiesCustomer2 -> Output6 +

                CustomerSelectsWithdraw -> Input7 +
                SystemRequestsAccType -> Output7 +
                CustomerSelectsAccType -> Input8 +
                SystemRequestsAmount -> Output8 +
                CustomerEntersAmount -> Input9 +
                SystemChecksMoneyOnHand -> SC4 +
                SystemApprovesTransaction2 -> SC5 +
                SystemDispensesCash -> SR8 +
                SystemPrintsReceipt2 -> SR9 +

                SystemNotifiesMoneyNA -> Output9 +
                SystemRequestsSmallerAmount -> Output10 +

                CustomerSelectsTransfer -> Input10 +
                SystemRequestsAccsAndAmount -> Output11 +
                CustomerEntersAccsAndAmount -> Input11 +
                SystemApprovesTransaction3 -> SC6 +
                SystemPrintsReceipt3 -> SR10
}
fact steps { stepID = CustomerInsertsCard -> Sid1 + SystemVerifiesCard -> Sid2 + SystemReadsCard -> Sid3 +
            SystemAsksPIN -> Sid4 + CustomerEntersPIN -> Sid5 + SystemRequestsOperation -> Sid6 +
            SystemAsksForMoreOps -> Sid7 + CustomerWantsNoMoreOps -> Sid8 + CustomerEntersNo -> Sid9 +
            SystemEjectsCard -> Sid10 + SystemTerminatesSession -> Sid11 + SystemEjectsCard2 -> Sid12 +
            SystemNotifiesCustomer -> Sid13 + CustomerEntersYes -> Sid14 + Success1 -> Sid15 +
            Goto6 -> Sid16 + Failure1 -> Sid17 + IncludePerformTransaction -> Sid18 +
                        
            CustomerSelectsTransaction -> Sid19 + SystemRequestsDetails -> Sid20 + CustomerEntersDetails -> Sid21 +
            SystemApprovesTransaction -> Sid22 + SystemPerformsAdequateSteps -> Sid23 + SystemPrintsReceipt -> Sid24 +

            SystemChecksFailedPINAttempts -> Sid25 + Goto4 -> Sid26 + SystemRetainsCard -> Sid27 + SystemNotifiesCustomer2 -> Sid28 +
            Failure2 -> Sid29 +

            CustomerSelectsWithdraw -> Sid30 + SystemRequestsAccType -> Sid31 + CustomerSelectsAccType -> Sid32 +
            SystemRequestsAmount -> Sid33 + CustomerEntersAmount -> Sid34 + SystemChecksMoneyOnHand -> Sid35 +
            SystemApprovesTransaction2 -> Sid36 + SystemDispensesCash -> Sid37 + SystemPrintsReceipt2 -> Sid38 + 
            SystemNotifiesMoneyNA -> Sid39 + SystemRequestsSmallerAmount -> Sid40 + GotoW4 -> Sid41 + 

            CustomerSelectsTransfer -> Sid42 + SystemRequestsAccsAndAmount -> Sid43 + CustomerEntersAccsAndAmount -> Sid44 +
            SystemApprovesTransaction3 -> Sid45 + SystemPrintsReceipt3 -> Sid46
}
fact gotos { otherStepID = Goto6 -> Sid6 + Goto4 -> Sid4 + GotoW4 -> Sid33 }
fact choices { Choice <: extensions = SC1 -> Eid1 + UC1 -> Eid2 + SC2 -> Eid3 + SC3 -> Eid4 + SC4 -> Eid5 + SC5 -> Eid3 + SC6 -> Eid3 }
fact includes { ucName = IncludePerformTransaction -> Name2 }
