open util/relation as rel
open util/ternary as ter
open linking_module as l

-- #Input = #m() Actor->Sistema
/*check { #(LinkingNode.linkedUC.mainScenario.flow.stepType[Int] & Input) +*/
/*        #(LinkingNode.linkedUC.mainScenario.flow.actionSteps.stepType[Int][Int] & Input) +*/
/*        #(LinkingNode.linkedUC.extensions.extensionScenario.flow.stepType[Int] & Input)*/
/*            =*/
/*        #({ m: (SystemSequenceDiagram.messages + Operand.messages)[Int] | m.source = SystemSequenceDiagram.actor and*/
/*                         m.target = SystemSequenceDiagram.system })*/
/*} for 10 but 5 int*/

-- #Output = #m() Sistema->Actor
/*check { #(LinkingNode.linkedUC.mainScenario.flow.stepType[Int] & Output) +*/
/*        #(LinkingNode.linkedUC.mainScenario.flow.actionSteps.stepType[Int][Int] & Output) +*/
/*        #(LinkingNode.linkedUC.extensions.extensionScenario.flow.stepType[Int] & Output)*/
/*            =*/
/*        #({ m: (SystemSequenceDiagram.messages + Operand.messages)[Int] | m.source = SystemSequenceDiagram.system and*/
/*                         m.target = SystemSequenceDiagram.actor })*/
/*} for 10 but 5 int*/

-- #SR+SC = #m() Sistema->Sistema
/*check { #(LinkingNode.linkedUC.mainScenario.flow.stepType[Int] & (SystemR+SystemCheck)) +*/
/*        #(LinkingNode.linkedUC.mainScenario.flow.actionSteps.stepType[Int][Int] & (SystemR+SystemCheck)) +*/
/*        #(LinkingNode.linkedUC.extensions.extensionScenario.flow.stepType[Int] & (SystemR+SystemCheck))*/
/*            =*/
/*        #({ m: (SystemSequenceDiagram.messages + Operand.messages)[Int] | m.source = SystemSequenceDiagram.system and*/
/*                         m.target = SystemSequenceDiagram.system })*/
/*} for 10 but 5 int*/

-- #Alt.History+UCException = #Break
/*check { #(LinkingNode.linkedUC.extensions.extensionScenario & (AltHistory+UCException)) */
/*            =*/
/*        #Break*/
/*} for 10 but 5 int*/

-- #Includes = #Ref
/*check { #(LinkingNode.linkedUC.mainScenario.flow[Int] & Include) +*/
/*        #(LinkingNode.linkedUC.extensions.extensionScenario.flow[Int] & Include)*/
/*            =*/
/*        #Ref*/
/*} for 10 but 5 int*/

-- #ConditionalInsertion = #Opt-Loop
fun flattenMainScenario[f : BasicFlow] : seq Step {
    { i:Int,s:Step |  }
}
check { #({ alt:AltFlow | one altPoint: Int | 
                altPoint = alt.~extensionScenario.id.~extensions.~stepType.~(ActionBlock.actionSteps) and
                alt.flow.otherStepID[Int] = 
                    alt.~extensionScenario.id.~extensions.~stepType.~(select13[actionSteps]).actionSteps[altPoint+1].stepID })
            =
        #Ref
} for 10 but 5 int

-- #InteractionCycle = #Loop
-- #InteractionFragment = #Alt
-- todas as mensagens do SSD devem ocorrer na mesma ordem dos respctivos ActionSteps do UC
/*run {} for 10 but 5 int*/
