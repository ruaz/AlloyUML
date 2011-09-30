open textualUseCase as uc
open SystemSequenceDiagram as ssd
/*open InteractionOverviewDiagram as iod*/

one sig LinkingNode {
    linkedUC: UseCase,
    linkedSSD: SystemSequenceDiagram
    /*linkedIOD: InteractionOverviewDiagram*/
} {
    linkedUC = PerformSession
    linkedSSD = PerformSessionSSD
    /*linkedIOD = PerformSessionIOD*/
}


