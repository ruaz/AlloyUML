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
abstract sig StepType{}
sig System extends StepType{}
sig Interaction extends StepType{}
sig Internal extends StepType{}
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
	stepType: one StepType,
	label: one Label,
	extensions: set ExtensionID
}
fact {	 bijective[stepType,StepType] }
fact { all uc: UseCase, e: Extension 
			| e.id in ran[uc.mainSuccessScenario.stepseq].(Atom <: extensions) +
						ran[uc.mainSuccessScenario.stepseq].(Choice <: extensions) +
						ran[uc.mainSuccessScenario.stepseq].(Concurrent <: extensions) 
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
	extensionScenario: StepSequence
}
fact { bijective[id, ExtensionID] } // Def. 1.1 os id's são únicos. 
											   //Def. 1.2 não há ExtensionID's sem um Extension
sig Condition{}
/* ************************************ */
/* Use Case */
sig UseCase {
	name: UCName,
	properties: one UCProperties,
	mainSuccessScenario: one StepSequence,
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
/* Helper Signatures */
sig StepSequence { stepseq: seq Step } { last[stepseq] in Goto + Success + Failure } //Def. 1.4
fact { all s:Step | s in univ.(univ.stepseq) } //para não haver Step's fora de StepSequences
/* ************************************ */
/* Helper Functions */
fun inclui : UseCase -> UseCase { 
	{ uc1,uc2 : UseCase | uc2 in name.(uc1.mainSuccessScenario.stepseq.ucName[univ]) }
}
/* ************************************ */

// Show
pred Show{ }
run Show for 3 but exactly 1 UseCaseModel
