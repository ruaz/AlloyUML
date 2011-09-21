/*numero de nodos de ligação igual ao numero de uc's do diagrama de uc's.*/
/*faz-se ligar cada nodo a cada uc. como?.. n vou importar o textualUseCase praqui (ou entao importo praqui e n importo pro checker)*/
/*cada nodo a cada a ssd e a cada iod tb*/
/*no fim indica-se o k se pretende verificar.*/

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


