module umlFormalModels/textualUseCase

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
abstract sig Input extends ActionStep {}
abstract sig Output extends ActionStep {}
abstract sig SystemR extends ActionStep {}
abstract sig Assume extends ActionStep {}
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
/* ************************************ */
/* Kinds of Steps */
abstract sig Step{ stepID: one StepID } { 
    // para não haver Steps soltos
    Step in /*Choice.alternatives[univ] + (retirados os passos Choice)*/
            /*Concurrent.steps +*/
            Flow.flow[univ]
    // um Step só pode aparecer uma vez num flow e apenas num único flow
    all s: Step | one flow.s
}
fact { bijective[stepID, StepID] } //Def. 1.1 os id's são únicos. Def. 1.2 não há StepID's sem um Step
/* Atom */
abstract sig Atom extends Step{
	stepType: one ActionStep,
	label: one Label,
	extensions: set ExtensionID
} {
	stepType not in Assume => #extensions = 0
}
fact { bijective[stepType,ActionStep] }

abstract sig StepID{}
abstract sig Label{}{ Label in Atom.label }
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
}
fact gotoNaoCiclicos { Goto.otherStepID & Goto.stepID = none }
/* Include */
abstract sig Include extends Step{
	ucName: one UCName
} {
    Include in univ.(UseCase.extensions.extensionScenario.flow + UseCase.mainSuccessScenario.flow)    
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
	extensionScenario: Flow
} {
	// pra não haver extensions soltos
	Extension in univ.extensions
}
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
	mainSuccessScenario: one Flow,
	extensions: set Extension
}{
	// o conj de extensions (alt flows) de um UC é igual ao conj de
	// extension dos seus passos
	extensions = { e: Extension | 
		e.id in ran[mainSuccessScenario.flow].(Atom <: extensions) +
		/*ran[mainSuccessScenario.flow].(Choice <: extensions) +*/
		/*ran[mainSuccessScenario.flow].(Concurrent <: extensions) +*/
        (ActionBlock <: ran[mainSuccessScenario.flow]).actionSteps[univ].(Atom <: extensions)}
    // um Goto não pode apontar para um passo fora do use case onde está. no entanto, como está agora, 
    // é permitido um Goto apontar para um passo de um fluxo alternativo.
    all g: Goto |
        g in (mainSuccessScenario.flow[univ] + extensions.extensionScenario.flow[univ]) =>
        g.otherStepID in mainSuccessScenario.flow[univ].stepID + extensions.extensionScenario.flow[univ].stepID
    // todos os UseCase têm de pertencer a algum UseCaseModel
    UseCase in UseCaseModel.useCases[univ]
}

fact { bijective[name, UCName] }

/* ************************************ */
/* Use Case Model (Def.1) */
abstract sig UseCaseModel {
	rootUCName: one UCName,
	useCases: UCName -> UseCase
}{
	rootUCName in dom[useCases]
	all n: UCName, u: UseCase | n -> u in useCases => n in u.name
}
/* ************************************ */
abstract sig ActionBlock {
	actionSteps: seq Atom
} {
	// os action blocks não podem estar vazios
	#actionSteps > 0
	// o 1º passo dos AB é sempre um Input
	first[actionSteps].stepType in Input
	// e é so o 1º, nunca aparece no corpo restante de um AB
	Input not in univ.(rest[actionSteps]).stepType
	// o Output, se aparecer, é sempre na última posição de um AB
	Output not in univ.(butlast[actionSteps]).stepType
	// os actionsBlocks tem de estar ligados a Flow's
	all ab: ActionBlock | some f: Flow | ab in f.flow[univ]

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
	Assume not in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}

abstract sig Validation extends ActionBlock {
	
} {
	some a: Assume | a in univ.actionSteps.stepType
	SystemR not in univ.actionSteps.stepType
	Output not in univ.actionSteps.stepType
}

abstract sig Complete extends ActionBlock {
	
} {
	last[actionSteps].stepType in Output
	some a: Assume | a in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}
/* ************************************ */
/* Helper Signatures */
abstract sig Flow { 
	flow: seq Step + ActionBlock
} { 
	//Def. 1.4
	last[flow] in Goto + Success + Failure
	// e só podem ser o último
	Goto + Success + Failure not in univ.(butlast[flow])
	// pra n haver flows soltos
	Flow in Extension.extensionScenario + UseCase.mainSuccessScenario
	// os flows têm de ter pelo menos dois passos (discutivel)
	#flow > 1
} 
/*fact { all s:Step | s in univ.(univ.flow) } //para não haver Step's fora de Flows*/
/* ************************************ */
/* Helper Functions */
fun inclui : UseCase -> UseCase { 
	{ uc1,uc2 : UseCase | uc2 in name.(uc1.mainSuccessScenario.flow.ucName[univ]) }
}
/* ************************************ */
/* Instância para teste */
/* Action blocks, action steps e steps gerais */
/*one sig Input1, Input2, Input3, Input4, Input5 extends Input {}*/
/*one sig Output1, Output2, Output3, Output4, Output5 extends Output {}*/
/*one sig Assume1, Assume2, Assume3, Assume4 extends Assume {}*/
/*one sig SystemR1 extends SystemR {}*/
/*one sig Query1, Query2 extends Query {}*/
/*one sig Complete1 extends Complete {}*/
/*one sig Atom1, Atom2, Atom3, Atom4, Atom5, Atom6, Atom7, Atom8, Atom9, Atom10, Atom11, Atom12, Atom13, Atom14, Atom15 extends Atom {}*/
/*one sig Label1, Label2, Label3, Label4, Label5, Label6, Label7, Label8, Label9, Label10, Label11, Label12, Label13, Label14, Label15 extends Label {}*/
/*/* Passos finais */
/*one sig Success1 extends Success {}*/
/*one sig Goto1, Goto8 extends Goto {}*/
/*one sig Failure1, Failure2 extends Failure {}*/
/*/* Use Case e entensões */
/*one sig UseCaseModel1 extends UseCaseModel {}*/
/*one sig UseCase1 extends UseCase {}*/
/*one sig UCName1 extends UCName {}*/
/*one sig Extension1, Extension2, Extension3, Extension4 extends Extension {}*/
/*one sig ExtensionID1, ExtensionID2, ExtensionID3, ExtensionID4 extends ExtensionID {}*/
/*one sig Condition1, Condition2, Condition3, Condition4 extends Condition {}*/
/*/* Flows */
/*one sig Flow1, Flow2, Flow3, Flow4, Flow5 extends Flow {}*/
/*/* Facts */
/*fact usecasemodel{ */
/*    rootUCName = UseCaseModel1 -> UCName1*/
/*    useCases = UseCaseModel1 -> UCName1 -> UseCase1*/
/*}*/
/*fact usecase { */
/*    name = UseCase1 -> UCName1*/
/*    mainSuccessScenario = UseCase1 -> Flow1*/
/*    extensions = UseCase1 -> (Extension1 + Extension2 + Extension3 + Extension4)*/
/*}*/
/*fact extensions{  */
/*    id = Extension1 -> ExtensionID1 + */
/*         Extension2 -> ExtensionID2 + */
/*         Extension3 -> ExtensionID3 +*/
/*         Extension4 -> ExtensionID4*/
/*    condition = Extension1 -> Condition1 +*/
/*                Extension2 -> Condition2 +*/
/*                Extension3 -> Condition3 +*/
/*                Extension4 -> Condition4*/
/*    extensionScenario = Extension1 -> Flow2 +*/
/*           Extension2 -> Flow3 +*/
/*           Extension3 -> Flow4 +*/
/*           Extension4 -> Flow5*/
/*}*/
/*fact actionsblocks{ */
/*    actionSteps = Query1 -> 0 -> Atom1 +*/
/*                  Query1 -> 1 -> Atom2 +*/
/**/
/*                  Query2 -> 0 -> Atom4 +*/
/*                  Query2 -> 1 -> Atom5 +*/
/*                  Query2 -> 2 -> Atom6 +*/
/*                  */
/*                  Complete1 -> 0 -> Atom8 +*/
/*                  Complete1 -> 1 -> Atom9 +*/
/*                  Complete1 -> 2 -> Atom10 +*/
/*                  Complete1 -> 3 -> Atom11*/
/*}*/
/*fact atoms{ */
/*    stepType = Atom1 -> Input1 + Atom2 -> Output1 +*/
/*               Atom3 -> Assume1 + Atom4 -> Input2 + */
/*               Atom5 -> Assume2 + Atom6 -> Output2 + */
/*               Atom7 -> Assume3 + Atom8 -> Input3 +                */
/*               Atom9 -> Assume4 + Atom10 -> SystemR1 +*/
/*               Atom11 -> Output3 + Atom12 -> Input4 + */
/*               Atom13 -> Output4 + Atom14 -> Input5 + */
/*               Atom15 -> Output5*/
/*               */
/*    label = Atom1 -> Label1 + Atom2 -> Label2 +*/
/*            Atom3 -> Label3 + Atom4 -> Label4 +*/
/*            Atom5 -> Label5 + Atom6 -> Label6 +*/
/*            Atom7 -> Label7 + Atom8 -> Label8 +*/
/*            Atom9 -> Label9 + Atom10 -> Label10 +*/
/*            Atom11 -> Label11 + Atom12 -> Label12 +*/
/*            Atom13 -> Label13 + Atom14 -> Label14 +*/
/*            Atom15 -> Label15 */
/**/
/**/
/*    extensions = Atom3 -> ExtensionID1 + Atom5 -> ExtensionID2 +*/
/*                 Atom7 -> ExtensionID3 + Atom9 -> ExtensionID4*/
/*}*/
/*fact flows { */
/*    flow = Flow1 -> 0 -> Query1 +*/
/*           Flow1 -> 1 -> Atom3 + */
/*           Flow1 -> 2 -> Query2 +*/
/*           Flow1 -> 3 -> Atom7 +*/
/*           Flow1 -> 4 -> Complete1 +*/
/*           Flow1 -> 5 -> Success1 +*/
/**/
/*           Flow2 -> 0 -> Atom12 +*/
/*           Flow2 -> 1 -> Goto1 + */
/*           */
/*           Flow3 -> 0 -> Atom13 +*/
/*           Flow3 -> 1 -> Failure1 + */
/**/
/*           Flow4 -> 0 -> Atom14 +*/
/*           Flow4 -> 1 -> Failure2 + */
/**/
/*           Flow5 -> 0 -> Atom15 +*/
/*           Flow5 -> 1 -> Goto8*/
/*}*/
// Show
run {} for 20 but exactly 3 Include, exactly 2 Goto
