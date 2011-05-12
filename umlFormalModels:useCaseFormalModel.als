module umlFormalModels/useCaseFormalModel 

sig Name{}

abstract sig Classifier{ name: one Name } 


abstract sig Actor extends Classifier{ inheritance: lone Actor }
sig User, ComputerSystem extends Actor{} 
-- invariants on actors
fact{
	AcyclicNoReflexive[Actor <: inheritance]
	noSymmetric[Actor <: inheritance]
	Actor<:inheritance in Actor lone -> lone Actor 
}
fact{ 
	all a: Actor |not isConnected[a] => some useCaseAssociatedWith[a]
}

sig UseCase extends Classifier{
	extend: set UseCase, -- TODO verficar se actor pode utilizar directamente
								   -- use cases de extensão
	extensionPoints: set ExtensionPoint,
	inheritance: set UseCase,
	include: set UseCase,
	scenarios: some ( MainSuccess + Extension )
}{
	#extend = #extensionPoints
	all e: extensionPoints | extend in e.useCase -- faz com que não haja mais que um
																	-- extend/extPt por use case
-- a use case can not be associated with 
-- two actors related with inheritance 
	--all u: useCases, disj a, a': use.u | a not in a'.^inheritance
	--all u: useCases, disj a, a': use.u | a not in a'.^inheritance
-- an actor can not be associated with two 
-- use cases having any relation 
	--all a: actors, disj u, u': use[a] | u not in elementsRelatedWith(u')
	all a: actors, disj u, u': use[a] |  u in elementsRelatedWith(u')
-- no parents of an actor associated with 
-- a use case can be associated with 
-- a use case
	--all a: actors | some use[a] => no use[ a.^inheritance ] 
	--all a: actors | some use[a] => no use[ a.^inheritance ] 
-- two actors related with inheritance can
-- not be associated with two use cases 
-- having any relation
	--all disj a, a': actors, disj u, u': useCases | {
		--a in a'.^inheritance
		--u in elementsRelatedWith(u') 
		--isAssociatedWith[u, a+a']
	--} => 
		--not isAssociatedWith[u',a+a']
 }

fun elementsRelatedWith(u': UseCase): set UseCase{ 
	u'.^extend + u'.^include + u'.^inheritance 
}
pred isAssociatedWith(u: UseCase, actors: set Actor){
	u in UseCaseModel.use[actors] 
}

abstract sig Scenario{}
sig MainSuccess extends Scenario{}
abstract sig Extension extends Scenario{}
sig Normal, Exceptional extends Extension{}

-- TODO todos os EP existentes têm que estar na lista de EPs de algum UC
-- TODO arranjar metamodelo UML oficial

assert so0OuUmExtPoint{
	all uc: UseCase | #uc.extensionPoints <=1
}

--check so0OuUmExtPoint for 10 but exactly 5 UseCase

sig ExtensionPoint{ 
	useCase: one UseCase 
}

sig UseCaseModel{ 
	actors: some Actor, 
	useCases: some UseCase,
	use: actors set -> set useCases, 
}

-- invariants on Name 
fact nameIsABijection{
	name in Classifier one -> one Name 
}

-- properties of the actor and use case relation
pred AcyclicNoReflexive(r: univ -> univ) { no iden & ^r}
pred noSymmetric(r: univ -> univ){ no ~r & r }

-- invariants on the extend relation of use cases
fact {
	AcyclicNoReflexive[extend]
	noSymmetric[extend]
}
-- invariants on the inheritance relation of use cases
fact{
	AcyclicNoReflexive[UseCase <: inheritance]
	noSymmetric[UseCase <: inheritance]
}
-- invariants on the include relation of use cases
fact{
	AcyclicNoReflexive[include]
	noSymmetric[include]
}
-- invariants on scenarios
fact scenariosIsAnInjectiveRelation{
	scenarios in UseCase one -> some Scenario
}
fact oneMainSuccessScenario{
	all u: UseCase | one s: u.scenarios | s in MainSuccess
}

-- invariants on the extension points 
--implícito mas escrito para documentação
fact useCaseIsATotalFunction{
--	useCase in ExtensionPoint set -> one UseCase 
}
fact noSelfCall{
	no u: UseCase | u in extensionPoints.useCase[u] 
}

fact extensionPointsIsAnInjectiveRelation{ 
	extensionPoints in UseCase lone -> set ExtensionPoint 
} 


fun parentsOf(a: Actor): lone Actor{
	a.(Actor<:inheritance)
}
fun childrenOf(a: Actor): lone Actor{
	(Actor<:inheritance).a
}
pred isConnected(a: Actor){
	some parentsOf[a] or some childrenOf[a]
}
fun useCaseAssociatedWith(a: Actor): set UseCase{
	UseCaseModel.use[a]
}

-- every actor is associated with either a
-- use case or with another actor
assert connectedActors{
	all a: Actor | some useCaseAssociatedWith[a]
					   or isConnected[a]
}
--check connectedActors for 6 but exactly 2 Actor, exactly 4 UseCase

pred showInstance(ucm: UseCaseModel){ 
	#ucm.useCases = 3
}

run showInstance for 5 but 1 UseCaseModel
