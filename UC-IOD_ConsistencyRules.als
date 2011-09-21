open util/relation as rel
open util/ternary as ter
open linking_module as l

-- #Alt.History+UCException = #nextNodes a entrar no FinalNode - 1 (do fluxo principal)
/*check { #(LinkingNode.linkedUC.extensions.extensionScenario & (AltHistory + UCException)) */
/*            =*/
/*        #(IODRef <: nextNode).FinalNode + #(IODSSD <: nextNode).FinalNode - 1*/
/*} for 10 but 5 int*/
-- #UCh+SC = #DecisionNode
/*check { #(LinkingNode.linkedUC.mainScenario.flow.stepType[Int] & Choice) +*/
/*        #(LinkingNode.linkedUC.mainScenario.flow.actionSteps.stepType[Int][Int] & Choice) +*/
/*        #(LinkingNode.linkedUC.extensions.extensionScenario.flow.stepType[Int] & Choice)*/
/*            =*/
/*        #DecisionNode*/
/*} for 10 but 5 int*/

-- #alternativas = #Condition-DecisionNode
/*check {*/
/*    #(LinkingNode.linkedUC.extensions) = #(l/iod/SystemSequenceDiagram/Condition) - #DecisionNode    */
/*} for 10 but 5 int*/

-- #ABs simples+Include < #Ref
/*check {*/
/*    #{ ab:LinkingNode.linkedUC.mainScenario.flow[Int] & ActionBlock | */
/*            all p:ab.actionSteps.stepType[Int] | p not in Choice } +*/
/*    #(LinkingNode.linkedUC.mainScenario.flow[Int] & Include) */
/*        <*/
/*    #IODRef*/
/*} for 10 but 5 int*/
-- ordem dos AB é igual à ordem dos Refs (mais Sd's)
/*check {*/
/*    */
/*}*/
