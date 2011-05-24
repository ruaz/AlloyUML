module umlFormalModels/textualUseCase

/*
* Adaptado de 'LTS Semantics for Use Case Models', por Daniel Sinnig
*/

open util/relation as rel
open util/ternary as ter

// Fig. 1
/* Goal Level Properties */
abstract sig GoalLvlProp{}
sig Summary extends GoalLvlProp{}
sig UserGoal extends GoalLvlProp{}
sig SubFunction extends GoalLvlProp{}
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
sig Assume extends ActionStep {}
/* ************************************ */
/* Use Case Properties */
sig UCProperties{
	goal: one GoalProperty,
	primaryActor: one ActorProperty,
	goalLevel: one GoalLvlProp,
	precondition: one PrecondProperty
}
//fact { bijective[goalLevel, GoalLvlProp] }

sig GoalProperty{}
sig ActorProperty{}
sig PrecondProperty{}
/* ************************************ */
/* Kinds of Steps */
abstract sig Step{ 	stepID: one StepID }
fact { bijective[stepID, StepID] } //Def. 1.1 os id's são únicos. Def. 1.2 não há StepID's sem um Step
/* Atom */
sig Atom extends Step{
	stepType: one ActionStep,
	label: one Label,
	extensions: set ExtensionID
}
fact { bijective[stepType,ActionStep] }
fact { all uc: UseCase, e: Extension 
			| e.id in ran[uc.mainSuccessScenario.flow].(Atom <: extensions) +
						ran[uc.mainSuccessScenario.flow].(Choice <: extensions) +
						ran[uc.mainSuccessScenario.flow].(Concurrent <: extensions) 
			=> e in uc.extensions } //todas as extensões de passos individuais estão contidas no useCase
sig StepID{}
sig Label{}
sig ExtensionID{}
/* Choice */
sig Choice extends Step{
	alternatives: set (seq Step),
	extensions: set ExtensionID
}
/* Concurrent */
sig Concurrent extends Step{
	steps: set (set Step),
	extensions: set ExtensionID
}
/* Goto */
sig Goto extends Step{
	otherStepID: one StepID
}
/* Include */
sig Include extends Step{
	ucName: one UCName
}
fact { ran[ucName] in mid[useCases] } //Def. 1.3 a)
fact { acyclic[inclui, UseCase] } // Def. 1.3 não há inclusoes ciclicas 
sig UCName{}
/* Success and Failure */
sig Success extends Step{ }
sig Failure extends Step{ }
/* ************************************ */
/* Extensions */
sig Extension {
	id: ExtensionID,
	condition: one Condition,
	extensionScenario: Flow
}
fact { bijective[id, ExtensionID] } // Def. 1.1 os id's são únicos. 
											   //Def. 1.2 não há ExtensionID's sem um Extension
sig Condition{}
/* ************************************ */
/* Use Case */
sig UseCase {
	name: UCName,
	properties: one UCProperties,
	mainSuccessScenario: one Flow,
	extensions: set Extension
}
fact { bijective[name, UCName] }

/* ************************************ */
/* Use Case Model (Def.1) */
sig UseCaseModel {
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
	#actionSteps > 0
	first[actionSteps].stepType in Input
	Input not in univ.(rest[actionSteps]).stepType
	Output not in univ.(butlast[actionSteps]).stepType
	// os actionsBlocks tem de estar ligados a Flow's
	all ab: ActionBlock | some f: Flow | ab in f.flow[univ]
}

sig Query extends ActionBlock {
	
} {
	last[actionSteps].stepType in Output
	// os passos intermédios só podem ser Assume's
	SystemR not in univ.actionSteps.stepType
}

sig Internal extends ActionBlock {
	
} {
	Output not in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}

sig Service extends ActionBlock {
	
} {
	last[actionSteps].stepType in Output
	Assume not in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}

sig Validation extends ActionBlock {
	
} {
	some a: Assume | a in univ.actionSteps.stepType
	SystemR not in univ.actionSteps.stepType
	Output not in univ.actionSteps.stepType
}

sig Complete extends ActionBlock {
	
} {
	last[actionSteps].stepType in Output
	some a: Assume | a in univ.actionSteps.stepType
	some s: SystemR | s in univ.actionSteps.stepType
}
/* ************************************ */
/* Helper Signatures */
sig Flow { 
	flow: seq Step + ActionBlock
} { 
	last[flow] in Goto + Success + Failure
} //Def. 1.4
fact { all s:Step | s in univ.(univ.flow) } //para não haver Step's fora de Flows
/* ************************************ */
/* Helper Functions */
fun inclui : UseCase -> UseCase { 
	{ uc1,uc2 : UseCase | uc2 in name.(uc1.mainSuccessScenario.flow.ucName[univ]) }
}
/* ************************************ */

// Show
pred Show{ }
run Show for 5 but exactly 1 UseCaseModel, exactly 1 ActionBlock,
exactly 5 Step
