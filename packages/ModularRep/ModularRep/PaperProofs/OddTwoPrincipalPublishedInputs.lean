import ModularRep.PaperProofs.OddTwoPrincipalCorrectedSeed

/-!
# The fixed published inputs for one intrinsic principal application

This bundles the existing licensed group, character, extension and standard
tuple inputs on the SAME D and standard predicate. It has no selected
reduction, authentic intrinsic interpretation, covariance, orbit witness,
correction input or seed field. In a Full-HG application D is the computed
family data and its interpretation is separately derived in K.

The downstairs convention is explicitly bound to D's one ambient table.
This does not identify independently chosen root conventions. The selected
quotient convention remains a separate family binding and K transport.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalPublishedInputs

open ModularRep ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoActualCentralInflationRelation
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness
open ModularRep.PaperProofs.OddTwoBroughCoveringSource
open ModularRep.PaperProofs.OddTwoBroughLemma46SourceAndPacket
open ModularRep.PaperProofs.OddTwoBroughPrincipalFourClauses
open ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions
open ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoPrincipalOrbitAdjustment
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
  (LiteralDiagonalFieldRealisation)

universe u

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]

local instance publishedGroupFintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (standard : BlockTripleSourceSemantics 2 k K)

/-- The existing external playlist with its literal dependent indices.
The E.iotaDown equality is the standard choice of the same finite root
table, independent of a selected weight, FM image or desired relation.
All substantial character/group laws retain their original source types. -/
structure PublishedInputs where
  DownBlock : Type u
  ConformalBlock : Type u
  [downBlockAction : MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ DownBlock]
  [conformalBlockAction : MulAction (MulAut (PCSp n F))ᵐᵒᵖ ConformalBlock]
  cover : OddSymplecticFullCoverSource n F
  descent : PrincipalDescentData (J := DownBlock) D cover
  downRoot_eq : descent.iotaDown =
    rootAt D (LiteralPSp n F) (projective_exponent_dvd cover)
  downSupport : OperationsBrauerSupport descent.iotaDown descent.downInjective
    descent.downSource.operations
  center : CenterIntersectionSource n F
  broughGroup : BroughGroupSource center
  fieldFixed : FengMalleCorollary43aSource D
  FM : D.FengMalleTheorem62LiteralCertificate
  lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F)
  conformalRoot : PrimeRegularRootEmbedding 2 k K (PCSp n F)
  conformalSource : LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := PCSp n F) (Block := ConformalBlock)
  conformalInjective : IrreducibleBrauerCharacterInjectivity conformalRoot
  dgn : DGNSourceSemantics (K := K) center broughGroup
  covering : BroughCoveringLaws (projectiveBaseNormal := broughGroup.normal_image)
    center broughGroup descent.iotaDown conformalRoot dgn
  blockCovering : BlockCoveringLaws center broughGroup descent.iotaDown conformalRoot
    descent.downSource conformalSource descent.downInjective conformalInjective dgn
  brough : BroughLemma46Source (projectiveBaseNormal := broughGroup.normal_image)
    broughGroup descent.iotaDown conformalRoot conformalSource conformalInjective dgn
    (BroughCoveringLaws.tensorFormula
      (projectiveBaseNormal := broughGroup.normal_image) covering) cover standard
  brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k
  ordinaryExtension : Representation.CyclicExtensionPrinciple.{u, u, u} K
  butterfly : OddTwoBroughButterflySource.MRRLemma311Source broughGroup standard
  quotientInterpretation : QuotientTupleInterpretation descent.brauer cover lifting
    descent.weightNaturality standard
  inflation : MRRLemma314Source standard
  standardTransport : StandardTransportSource standard
  diagonalField : LiteralDiagonalFieldRealisation n F
  multiplier : ProjectiveMultiplierSource center
  globalRoots : ∀ psi : descent.DownPrincipalBrauer,
    GlobalRoots broughGroup descent.iotaDown psi.1

attribute [instance] PublishedInputs.downBlockAction PublishedInputs.conformalBlockAction

namespace PublishedInputs

variable {D standard} (S : PublishedInputs D standard)
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)

/-- The selected clause is supplied by the separately checked transport of
the fixed FAMILY table. The downstairs clause is the explicit source choice. -/
def commonRootConvention
    (selected : ∀ w : D.PrincipalWeight,
      (OddTwoDefinition35OwnReduction.selectedQuotientReduction D reduction w).iota =
        rootAt D (NormalizerQuotient (OddTwoDefinition35OwnReduction.weightRepresentative D w).subgroup)
          (upQuotient_exponent_dvd D w)) :
    CommonRootConvention D reduction S.cover S.descent.iotaDown where
  downRoot_eq := S.downRoot_eq
  selectedRoot_eq := selected

variable (rootConvention : CommonRootConvention D reduction S.cover S.descent.iotaDown)
variable (flz : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
variable (meaning : AuthenticDefinition35Interpretation D reduction flz standard)

/-- K application of the checked engine to this exact playlist. The same
derived meaning supplies both the Brough and covariance lanes. -/
def correctionInput : PrincipalOrbitCorrectionInput D reduction S.FM flz :=
  OddTwoPrincipalCorrectedSeed.correctionInput D reduction S.descent rootConvention
    S.downSupport S.broughGroup S.fieldFixed S.FM S.lifting S.conformalRoot
    S.conformalSource S.conformalInjective S.dgn S.covering S.blockCovering
    standard S.brough S.brauerExtension S.ordinaryExtension S.butterfly
    S.quotientInterpretation S.inflation flz meaning S.standardTransport
    S.diagonalField S.multiplier S.globalRoots

/-- The seed is constructed; it is absent from PublishedInputs. -/
def principalSeed :
    Definition35IBAWBijection (D.problem reduction) (D.automorphisms reduction) flz :=
  (S.correctionInput reduction rootConvention flz meaning).definition35Seed

end PublishedInputs

end ModularRep.PaperProofs.OddTwoPrincipalPublishedInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
