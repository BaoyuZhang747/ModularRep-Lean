import ManuscriptIBAW.TypeC.PrincipalAutomorphisms
import ManuscriptIBAW.TypeC.PrincipalGGGR
import ModularRep.PaperProofs.OddTwoPrincipalPublishedInputs

/-!
# Principal application inputs with a constructed correspondence

The assumptions on primitive blocks, roots, covers, extensions and modular
character triples are indexed by the specified principal data. The parameter
construction and local action formulas determine the principal correspondence.
Field invariance of principal block Brauer characters and the numerical
counts are explicit Feng–Malle assumptions. The GGGR character selection is
proved separately and is not used to derive these assumptions.

The ordinary character field is fixed by these data. This construction makes
no identification with the fraction field of a complete discrete valuation
ring.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.OddTwoFYZPrincipalFullCarrierJoin
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation (PCSp)
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
open ModularRep.PaperProofs.OddTwoPrincipalPublishedInputs
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
  (LiteralDiagonalFieldRealisation)

universe u

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]

local instance applicationGroupFintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))

/-- The hypotheses for the principal parameter construction. The field and
diagonal calculations use the acting groups fixed by the principal data. -/
structure PrincipalReconstructionInputs (fieldOdd : Odd (Nat.card F))
    (O : LiteralDiagonalFieldRealisation n F) where
  Index : Type u
  core : DefectZeroCoreSource (n := n) (F := F) (K := K)
  criterion : FYZPrincipalCriterion D
  atlas : Index → PrincipalProductData (n := n) (F := F) (K := K)
  classification : PrincipalProductClassification atlas
  lemma23 : FYZLemma23IntrinsicCertificate D
  factors : PrincipalFactorSelection D
  coordinates : FMProductCoordinates atlas
  multiplicities : coordinates.MultiplicityClassification
  weightFields : ∀ sigma : F ≃+* F,
    FMParameterActionSource fieldOdd core atlas coordinates multiplicities
      (ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation.spFieldAut
        (n := n) sigma) id
  diagonalAction : FMParameterActionSource fieldOdd core atlas coordinates multiplicities
    (principalDiagonal O) (fmParameterDiagonal n)

namespace PrincipalReconstructionInputs

variable {D} {fieldOdd : Odd (Nat.card F)} {O : LiteralDiagonalFieldRealisation n F}
variable (I : PrincipalReconstructionInputs D fieldOdd O)

/-- Construct the principal correspondence data from the parameter bijection and
the finite orbit arguments on the specified principal fibres. -/
def correspondence (groups : PrincipalAutomorphismSource O)
    (fieldFixed : FengMalleCorollary43aSource D)
    (counts : FMPrincipalCountSource D (principalDiagonal O)) :
    D.FengMalleTheorem62LiteralCertificate :=
  principalCorrespondence D fieldOdd I.core I.criterion I.atlas I.classification I.lemma23
    I.factors I.coordinates I.multiplicities O groups fieldFixed I.weightFields
    I.diagonalAction counts

end PrincipalReconstructionInputs

variable (standard : BlockTripleSourceSemantics 2 k K)

/-- The parameters construct the principal correspondence. The published
covering, extension and modular character triple assumptions concern the
same specified root and block operations. -/
structure PrincipalApplicationPublishedInputs where
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
  center : ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation.CenterIntersectionSource n F
  broughGroup : ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation.BroughGroupSource center
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
  butterfly : ModularRep.PaperProofs.OddTwoBroughButterflySource.MRRLemma311Source
    broughGroup standard
  quotientInterpretation : QuotientTupleInterpretation descent.brauer cover lifting
    descent.weightNaturality standard
  inflation : MRRLemma314Source standard
  standardTransport : StandardTransportSource standard
  diagonalField : LiteralDiagonalFieldRealisation n F
  principalCharacters : PrincipalGGGR.PrincipalSource D (principalDiagonal diagonalField)
  multiplier : ProjectiveMultiplierSource center
  globalRoots : ∀ psi : descent.DownPrincipalBrauer,
    GlobalRoots broughGroup descent.iotaDown psi.1
  reconstruction : PrincipalReconstructionInputs D cover.field_odd diagonalField

attribute [instance] PrincipalApplicationPublishedInputs.downBlockAction
  PrincipalApplicationPublishedInputs.conformalBlockAction

namespace PrincipalApplicationPublishedInputs

variable {D standard} (S : PrincipalApplicationPublishedInputs D standard)

include S in
/-- The explicit assumption of Feng–Malle Corollary 4.3(a). -/
theorem fieldFixed : FengMalleCorollary43aSource D := S.principalCharacters.fieldFixed

include S in
/-- The explicit principal block counts used in the finite orbit argument. -/
theorem counts : FMPrincipalCountSource D (principalDiagonal S.diagonalField) :=
  S.principalCharacters.counts

/-- The constructed correspondence used in the subsequent principal arguments. -/
def correspondence : D.FengMalleTheorem62LiteralCertificate :=
  S.reconstruction.correspondence
    (principalAutomorphismSourceFromGeometry S.broughGroup S.diagonalField S.multiplier
      S.cover S.lifting) S.fieldFixed S.counts

/-- Use the principal correspondence proved above together with the stated
assumptions on primitive blocks, covers and extensions. -/
def toPublishedInputs : PublishedInputs D standard where
  DownBlock := S.DownBlock
  ConformalBlock := S.ConformalBlock
  downBlockAction := S.downBlockAction
  conformalBlockAction := S.conformalBlockAction
  cover := S.cover
  descent := S.descent
  downRoot_eq := S.downRoot_eq
  downSupport := S.downSupport
  center := S.center
  broughGroup := S.broughGroup
  fieldFixed := S.fieldFixed
  FM := S.correspondence
  lifting := S.lifting
  conformalRoot := S.conformalRoot
  conformalSource := S.conformalSource
  conformalInjective := S.conformalInjective
  dgn := S.dgn
  covering := S.covering
  blockCovering := S.blockCovering
  brough := S.brough
  brauerExtension := S.brauerExtension
  ordinaryExtension := S.ordinaryExtension
  butterfly := S.butterfly
  quotientInterpretation := S.quotientInterpretation
  inflation := S.inflation
  standardTransport := S.standardTransport
  diagonalField := S.diagonalField
  multiplier := S.multiplier
  globalRoots := S.globalRoots

@[simp] theorem toPublishedInputs_FM : S.toPublishedInputs.FM = S.correspondence := rfl

@[simp] theorem toPublishedInputs_down_root :
    S.toPublishedInputs.descent.iotaDown = S.descent.iotaDown := rfl

@[simp] theorem toPublishedInputs_diagonal :
    S.toPublishedInputs.diagonalField = S.diagonalField := rfl

variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable (rootConvention : CommonRootConvention D reduction S.cover S.descent.iotaDown)
variable (flz : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
variable (meaning : AuthenticDefinition35Interpretation D reduction flz standard)

/-- Apply orbit correction to the constructed correspondence, its selected
weights and the specified interpretation of all admissible tuples. -/
def correctionInput : PrincipalOrbitCorrectionInput D reduction S.correspondence flz :=
  S.toPublishedInputs.correctionInput reduction rootConvention flz meaning

/-- Correct the principal correspondence to satisfy the modular character triple
relation. The corrected map need not equal the initial counting bijection. -/
def principalSeed :
    Definition35IBAWBijection (D.problem reduction) (D.automorphisms reduction) flz :=
  (S.correctionInput reduction rootConvention flz meaning).definition35Seed

end PrincipalApplicationPublishedInputs

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
