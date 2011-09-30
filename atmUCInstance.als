module atmUCInstance

open util/relation
open util/ternary

// Entities
one sig ATMUseCaseModel extends UseCaseModel {}    
/* ************************************ */
one sig Customer extends User {}    
/* ************************************ */
one sig PerformSession, PerformTransaction, HandleInvalidPIN, WithdrawMoney, TransferMoney, InsertPIN extends UseCase {}    
/* ************************************ */
one sig Alt1,Alt2,Alt3,Alt4,Alt5 extends Alternative {}
/* ************************************ */
one sig Flow1 extends BasicFlow {}
one sig Exception1,Exception2 extends UCException {}
one sig AltPart1,AltPart2 extends AltPart {}    
one sig InsertionFlow1,InsertionFlow2,InsertionFlow3,InsertionFlow4 extends InsertionFlow {}    
/* ************************************ */
one sig SystemCantReadCard,CustomerWantsMoreOps,OneOrTwoFailedPinAttempts,ThreeFailedPinAttempts,NotEnoughMoneyOnHand extends Condition {}
/* ************************************ */
/*one sig Complete1 extends Complete {}    */
/*one sig Query1,Query2,Query3,Query4,Query5 extends Query {}    */
/*one sig Internal1,Internal2,Internal3,Internal4 extends Internal {}    */
/*one sig Validation1 extends Validation {}    */
/*/* ************************************ */
/*PerformSession*/
one sig CustomerInsertsCard,SystemVerifiesCard,SystemReadsCard,SystemAsksPIN,
    CustomerEntersNo,SystemEjectsCard,SystemTerminatesSession extends Atom {}
one sig IncludePerformTransaction extends Include {}    
/*2a.Exception*/
one sig SystemEjectsCard2,SystemNotifiesCustomer extends Atom {}    
/*5a.AltPart*/
one sig CustomerEntersYes,SystemRequestsTransaction extends Atom {}    
one sig Goto5 extends Goto {}    
/*Choices*/
one sig SystemValidation1 extends SystemValidation {}    
one sig UserDecision1 extends UserDecision {}    
/*StepIDs and AlternativeIDs*/
one sig Sid1,Sid2,Sid3,Sid4,Sid5,Sid6,Sid7,Sid8,Sid9,Sid10,Sid11,Sid12,Sid13,Sid14 extends StepID {}    
one sig Aid1,Aid2 extends AlternativeID {}    
/*UC Name*/
one sig Name1 extends UCName {}    
/*/* ************************************ */
/*/*PerformTransaction*/
/*/*ActionSteps*/
/*/*StepIDs and AlternativeIDs*/
one sig Aid3 extends AlternativeID {}    
/*UC Name*/
one sig Name2 extends UCName {}    
/*/* ************************************ */
/*/*HandleInvalidPIN*/
one sig SystemRequestsPinAgain,CustomerReentersPin,SystemValidatesPin extends Atom {}    
/*/*1a.Exception*/
one sig SystemRetainsCard,SystemNotifiesCustomer2,SystemTerminatesSession2 extends Atom {}    
/*Choices*/
one sig SystemValidation2 extends SystemValidation {}    
/*/*stepIDs and AlternativeIDs*/
one sig Sid15,Sid16,Sid17,Sid18,Sid19,Sid20,Sid21,Sid22 extends StepID {}    
one sig Aid4 extends AlternativeID {}    
/*UC Name*/
one sig Name3 extends UCName {}    
/*/* ************************************ */
/*/*WithdrawMoney*/
one sig CustomerSelectsWithdraw,SystemRequestsAccType,CustomerSelectsAccType,SystemRequestsAmount,CustomerEntersAmount,SystemChecksMoneyOnHand,
        SystemChecksPIN1,SystemDispensesCash,SystemPrintsReceipt2,SystemAsksForMoreTr extends Atom {}    
one sig IncludeInsertPIN extends Include {}    
/*/*5a.AltPart*/
one sig SystemNotifiesMoneyNA,SystemRequestsSmallerAmount extends Atom {}    
one sig Goto6 extends Goto {}
/*Choices*/
one sig SystemValidation3,SystemValidation4 extends SystemValidation {}    
/*/*stepIDs and AlternativeIDs*/
one sig Sid23,Sid24,Sid25,Sid26,Sid27,Sid28,Sid29,Sid30,Sid31,Sid32,Sid33,Sid34,Sid35,Sid36 extends StepID {}    
one sig Aid5 extends AlternativeID {}    
/*UC Name*/
one sig Name4 extends UCName {}    
/* ************************************ */
/*TransferMoney*/
one sig CustomerSelectsTransfer,SystemRequestsAccsAndAmount,CustomerEntersAccsAndAmount,SystemChecksPIN2,
        SystemPrintsReceipt3,SystemAsksForMoreTr2 extends Atom {}    
one sig IncludeInsertPIN2 extends Include {}    
/*Choices*/
one sig SystemValidation5 extends SystemValidation {}    
/*stepIDs*/
one sig Sid37,Sid38,Sid39,Sid40,Sid41 extends StepID {}
/*UC Name*/
one sig Name5 extends UCName {}    
/* ************************************ */
/*InsertPIN*/
one sig CustomerInsertsPin,SystemRequestsTransaction2 extends Atom {}    
/*stepIDs*/
one sig Sid42,Sid43,Sid44,Sid45 extends StepID {}    
/*UC Name*/
one sig Name6 extends UCName {}    
/* ************************************ */
fact ucmodel { actors = ATMUseCaseModel -> Customer
               use = ATMUseCaseModel -> Customer -> PerformSession
               useCases = ATMUseCaseModel -> Name1 -> PerformSession + ATMUseCaseModel -> Name2 -> PerformTransaction +
                         ATMUseCaseModel -> Name3 -> HandleInvalidPIN + ATMUseCaseModel -> Name4 -> WithdrawMoney +
                         ATMUseCaseModel -> Name5 -> TransferMoney + ATMUseCaseModel -> Name6 -> InsertPIN}
fact usecases { goalLevel = PerformSession -> USERGOAL + PerformTransaction -> SUBFUNCTION + HandleInvalidPIN -> SUBFUNCTION + 
                    WithdrawMoney -> SUBFUNCTION + TransferMoney -> SUBFUNCTION + InsertPIN -> SUBFUNCTION
                alternatives = PerformSession -> Alt1 + PerformSession -> Alt2 + HandleInvalidPIN -> Alt4 + 
                    WithdrawMoney -> Alt3 + WithdrawMoney -> Alt5 + TransferMoney -> Alt3
                name = PerformSession -> Name1 + PerformTransaction -> Name2 + HandleInvalidPIN -> Name3 + WithdrawMoney -> Name4 +
                    TransferMoney -> Name5 + InsertPIN -> Name6
                mainScenario = PerformSession -> Flow1 + PerformTransaction -> EmptyFlow + HandleInvalidPIN -> InsertionFlow1 + 
                WithdrawMoney -> InsertionFlow2 + TransferMoney -> InsertionFlow3 + InsertPIN -> InsertionFlow4
                inheritsFrom = WithdrawMoney -> PerformTransaction + TransferMoney -> PerformTransaction}
fact alternatives { condition = Alt1 -> SystemCantReadCard + Alt2 -> CustomerWantsMoreOps + Alt3 -> OneOrTwoFailedPinAttempts + 
                    Alt4 -> ThreeFailedPinAttempts + Alt5 -> NotEnoughMoneyOnHand
                  type = Alt1 -> INTERNAL + Alt2 -> INTERNAL + Alt3 -> EXTERNAL + Alt4 -> INTERNAL + Alt5 -> INTERNAL
                  alternativeScenario = Alt1 -> Exception1 + Alt2 -> AltPart1 + Alt3 -> InsertionFlow1 + Alt4 -> Exception2 +
                      Alt5 -> AltPart2
                  id = Alt1 -> Aid1 + Alt2 -> Aid2 + Alt3 -> Aid3 + Alt4 -> Aid4 + Alt5 -> Aid5 }
/*fact flows { flow =*/
/*                    --basic flows*/
/*                    Flow1 -> 0 -> Complete1 + */
/*                    Flow1 -> 1 -> IncludePerformTransaction +*/
/*                    Flow1 -> 2 -> Internal1 +*/
/*                    Flow1 -> 3 -> Success +*/
/**/
/*                    --insertion flows*/
/*                    InsertionFlow1 -> 0 -> SystemRequestsPinAgain +*/
/*                    InsertionFlow1 -> 1 -> Validation1 +*/
/*                    InsertionFlow1 -> 2 -> Resume +*/
/**/
/*                    InsertionFlow2 -> 0 -> Query1 +*/
/*                    InsertionFlow2 -> 1 -> Query2 +*/
/*                    InsertionFlow2 -> 2 -> Internal2 +*/
/*                    InsertionFlow2 -> 3 -> Resume +*/
/**/
/*                    InsertionFlow3 -> 0 -> Query3 +*/
/*                    InsertionFlow3 -> 1 -> Internal3 +*/
/*                    InsertionFlow3 -> 2 -> Resume +*/
/*                    */
/*                    InsertionFlow4 -> 0 -> Query4 +*/
/*                    InsertionFlow4 -> 1 -> Internal3 +*/
/*                    InsertionFlow4 -> 2 -> Resume +*/
/**/
/*                    --alt flows*/
/*                    Exception1 -> 0 -> SystemEjectsCard2 +*/
/*                    Exception1 -> 1 -> SystemNotifiesCustomer +*/
/*                    Exception1 -> 2 -> Failure +*/
/**/
/*                    AltPart1 -> 0 -> CustomerEntersYes +*/
/*                    AltPart1 -> 1 -> SystemRequestsTransaction +*/
/*                    AltPart1 -> 2 -> Goto5 +*/
/**/
/*                    Exception2 -> 0 -> SystemRetainsCard +*/
/*                    Exception2 -> 1 -> SystemNotifiesCustomer2 +*/
/*                    Exception2 -> 2 -> SystemTerminatesSession2 +*/
/*                    Exception2 -> 3 -> Failure*/
/*}*/
/*fact actionBlocks { actionSteps = Complete1 -> 0 -> CustomerInsertsCard + */
/*                    Complete1 -> 1 -> SystemVerifiesCard +*/
/*                    Complete1 -> 2 -> SystemReadsCard +*/
/*                    Complete1 -> 3 -> SystemAsksPIN +*/
/*                    Internal1 -> 0 -> CustomerEntersNo +*/
/*                    Internal1 -> 1 -> SystemEjectsCard +*/
/*                    Internal1 -> 2 -> SystemTerminatesSession +*/
/**/
/*                    Query1 -> 0 -> CustomerSelectsWithdraw +*/
/*                    Query1 -> 1 -> SystemRequestsAccType +*/
/*                    Query2 -> 0 -> CustomerSelectsAccType +*/
/*                    Query2 -> 1 -> SystemRequestsAmount +*/
/*                    Internal2 -> 0 -> CustomerEntersAmount +*/
/*                    Internal2 -> 1 -> SystemChecksMoneyOnHand +*/
/*                    Internal2 -> 2 -> SystemChecksPIN1 +*/
/*                    Internal2 -> 3 -> SystemDispensesCash +*/
/*                    Internal2 -> 4 -> SystemPrintsReceipt2 +*/
/*                    Internal2 -> 5 -> SystemAsksForMoreTr +*/
/**/
/*                    Query3 -> 0 -> CustomerSelectsTransfer +*/
/*                    Query3 -> 1 -> SystemRequestsAccsAndAmount +*/
/*                    Internal3 -> 0 -> CustomerEntersAccsAndAmount +*/
/*                    Internal3 -> 1 -> SystemChecksPIN2 +*/
/*                    Internal3 -> 2 -> SystemPrintsReceipt3 +*/
/*                    Internal3 -> 3 -> SystemAsksForMoreTr2 +*/
/**/
/*                    Query4 -> 0 -> CustomerInsertsPin +*/
/*                    Query4 -> 1 -> SystemRequestsTransaction */
/*}*/
/*fact atoms { stepType = CustomerInsertsCard -> Input +*/
/*               SystemVerifiesCard -> SystemValidation1 +*/
/*               SystemReadsCard -> SystemR +*/
/*               SystemAsksPIN -> Output +*/
/*               CustomerEntersNo -> UserDecision1 +*/
/*               SystemEjectsCard -> SystemR +*/
/*               SystemTerminatesSession -> SystemR +*/
/**/
/*               SystemEjectsCard2 -> SystemR +*/
/*               SystemNotifiesCustomer -> Output +*/
/**/
/*               CustomerEntersYes -> Input +*/
/**/
/*               SystemRequestsPinAgain -> Output +*/
/*               CustomerReentersPin -> Input +*/
/*               SystemValidatesPin -> SystemValidation2 +*/
/**/
/*               SystemRetainsCard -> SystemR +*/
/*               SystemNotifiesCustomer2 -> Output +*/
/*               SystemTerminatesSession2 -> SystemR +*/
/**/
/*                CustomerSelectsWithdraw -> Input +*/
/*                SystemRequestsAccType -> Output +*/
/*                CustomerSelectsAccType -> Input +*/
/*                SystemRequestsAmount -> Output +*/
/*                CustomerEntersAmount -> Input +*/
/*                SystemChecksMoneyOnHand -> SystemValidation3 +*/
/*                SystemChecksPIN1 -> SystemValidation4 +*/
/*                SystemDispensesCash -> SystemR +*/
/*                SystemPrintsReceipt2 -> SystemR +*/
/*                SystemAsksForMoreTr -> Output +*/
/**/
/*                SystemNotifiesMoneyNA -> Output +*/
/*                SystemRequestsSmallerAmount -> Output +*/
/**/
/*                CustomerSelectsTransfer -> Input +*/
/*                SystemRequestsAccsAndAmount -> Output +*/
/*                CustomerEntersAccsAndAmount -> Input +*/
/*                SystemChecksPIN2 -> SystemValidation5 +*/
/*                SystemPrintsReceipt3 -> SystemR*/
/*                SystemAsksForMoreTr2 -> Output +*/
/*}*/
fact steps { stepID = CustomerInsertsCard -> Sid1 + SystemVerifiesCard -> Sid2 + SystemReadsCard -> Sid3 +
            SystemAsksPIN -> Sid4 + CustomerEntersNo -> Sid5 + SystemEjectsCard -> Sid6 + SystemTerminatesSession -> Sid7 
            + SystemEjectsCard2 -> Sid8 + SystemNotifiesCustomer -> Sid9 + CustomerEntersYes -> Sid10 + 
            SystemRequestsTransaction -> Sid11 + Goto5 -> Sid12 + IncludePerformTransaction -> Sid13 +
                        
            SystemRequestsPinAgain -> Sid14 + CustomerReentersPin -> Sid15 + SystemValidatesPin -> Sid16 + 
            SystemRetainsCard -> Sid17 + SystemNotifiesCustomer2 -> Sid18 + SystemTerminatesSession2 -> Sid19 +

            CustomerSelectsWithdraw -> Sid20 + SystemRequestsAccType -> Sid21 + CustomerSelectsAccType -> Sid22 +
            SystemRequestsAmount -> Sid23 + CustomerEntersAmount -> Sid24 + SystemChecksMoneyOnHand -> Sid25 +
            SystemChecksPIN1 -> Sid26 + SystemDispensesCash -> Sid27 + SystemPrintsReceipt2 -> Sid28 + 
            SystemNotifiesMoneyNA -> Sid29 + SystemRequestsSmallerAmount -> Sid30 + Goto6 -> Sid31 + IncludeInsertPIN -> Sid32 +

            CustomerSelectsTransfer -> Sid33 + SystemRequestsAccsAndAmount -> Sid34 + CustomerEntersAccsAndAmount -> Sid35 +
            SystemChecksPIN2 -> Sid36 + SystemPrintsReceipt3 -> Sid37 + IncludeInsertPIN2 -> Sid38 +

            CustomerInsertsPin -> Sid39 + SystemRequestsTransaction2 -> Sid40 + Success -> Sid41 + Failure -> Sid42 + Resume -> Sid43 +
            SystemAsksForMoreTr -> Sid44 + SystemAsksForMoreTr2 -> Sid45
}
fact gotos { otherStepID = Goto5 -> Sid13 + Goto6 -> Sid24 }
fact choices { Choice <: alternatives = SystemValidation1 -> Aid1 + UserDecision1 -> Aid2 + SystemValidation2 -> Aid4 + 
                                        SystemValidation3 -> Aid5 + SystemValidation4 -> Aid3 + SystemValidation5 -> Aid3 }
fact includes { ucName = IncludePerformTransaction -> Name2 + IncludeInsertPIN -> Name6 + IncludeInsertPIN2 -> Name6 }
