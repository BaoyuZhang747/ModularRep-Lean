import ModularRep.PaperProofs.OddTwoPrincipalBroughOrbitWitness
import ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance

/-!
# The principal corrected seed from the actual source inputs

The same authentic Definition 3.5 interpretation is used for both the
Brough relation and covariance. Joint own reductions and their horizontal
root compatibility are computed from the fixed common-root convention.
The Brough theorem produces the orbit witness; the actual diagonal action
supplies involutivity and commutation. These proved fields construct the
existing orbit-correction input and hence its corrected principal seed.

No seed, orbit witness, covariance or matched relation is a source field.
The standard published source inputs remain explicit. Transport to every
relative full-H_G carrier is a separate construction, not asserted here.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalCorrectedSeed

open ModularRep
open ModularRep.CharacterWeight
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
open ModularRep.PaperProofs.OddTwoPrincipalDiagonalOrbitActions
open ModularRep.PaperProofs.OddTwoPrincipalBroughOrbitWitness
open ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions
open ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoPrincipalOrbitAdjustment
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
  (LiteralDiagonalFieldRealisation)

universe u

variable {n : ℕ} {F k K Block J BlockT : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]
variable [MulAction (MulAut (PCSp n F))ᵐᵒᵖ BlockT]

local instance seedGroupFintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)
variable (rootConvention : CommonRootConvention D reduction cover E.iotaDown)

/-- Joint root data for the orbit theorem are computed from the exact
selected quotient roots and the same fixed ambient convention. -/
def selectedPairRootData (w : D.PrincipalWeight) :
    SelectedPairRootData D reduction E w where
  pair := compatiblePairReductions D reduction cover E.iotaDown rootConvention w
  selectedCompatible := OddTwoCommonRootSelectedPairReductions.selectedCompatible
    D reduction cover E.iotaDown rootConvention w

variable (downSupport : OperationsBrauerSupport E.iotaDown E.downInjective
  E.downSource.operations)
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (fixed : FengMalleCorollary43aSource D)
variable (FM : D.FengMalleTheorem62LiteralCertificate)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))
variable (iotaT : PrimeRegularRootEmbedding 2 k K (PCSp n F))
variable (OT : LocalBlockInductionSource
  (p := 2) (k := k) (K := K) (G := PCSp n F) (Block := BlockT))
variable (injT : IrreducibleBrauerCharacterInjectivity iotaT)
variable (A : DGNSourceSemantics (K := K) C S)
variable (laws : BroughCoveringLaws (projectiveBaseNormal := S.normal_image)
  C S E.iotaDown iotaT A)
variable (blocks : BlockCoveringLaws C S E.iotaDown iotaT
  E.downSource OT E.downInjective injT A)
variable (standard : BlockTripleSourceSemantics 2 k K)
variable (brough : BroughLemma46Source (projectiveBaseNormal := S.normal_image)
  S E.iotaDown iotaT OT injT A
  (BroughCoveringLaws.tensorFormula (projectiveBaseNormal := S.normal_image) laws)
  cover standard)
variable (brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
variable (ordinaryExtension : Representation.CyclicExtensionPrinciple.{u, u, u} K)
variable (butterfly : OddTwoBroughButterflySource.MRRLemma311Source S standard)
variable (quotientInterpretation :
  QuotientTupleInterpretation E.brauer cover L E.weightNaturality standard)
variable (inflation : MRRLemma314Source standard)
variable (flz : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
variable (meaning : AuthenticDefinition35Interpretation D reduction flz standard)
variable (standardTransport : StandardTransportSource standard)
variable (O : LiteralDiagonalFieldRealisation n F)
variable (M : ProjectiveMultiplierSource C)
variable (globalRoots : ∀ psi : E.DownPrincipalBrauer, GlobalRoots S E.iotaDown psi.1)

/-- Every field of the existing correction input is now produced by the
actual K joins and their precisely licensed published source consumers.
In particular neither the orbit witness nor covariance is an argument. -/
def correctionInput : PrincipalOrbitCorrectionInput D reduction FM flz where
  diagonal := diagonalGamma (D := D) (O := O) (reduction := reduction)
  brauer_involutive := diagonalGamma_involutive
    (D := D) (reduction := reduction) (cover := cover) (S := S) (L := L) (O := O) (M := M)
  diagonal_commutes := fun a psi => diagonalGamma_commutes
    (D := D) (reduction := reduction) (E := E) (downSupport := downSupport)
    (S := S) (O := O) (fixed := fixed) a psi
  relation_covariant := definition35_covariant D reduction flz standard
    cover E.iotaDown rootConvention meaning standardTransport
  orbitWitness := OddTwoPrincipalBroughOrbitWitness.orbitWitness
    D reduction E downSupport S fixed FM L iotaT OT injT A laws blocks standard brough
    brauerExtension ordinaryExtension butterfly quotientInterpretation inflation flz
    meaning.toTupleInterpretation O M globalRoots
    (selectedPairRootData D reduction E rootConvention)

/-- Apply the existing constructive orbit correction to the original FM
map. This is a seed on the exact intrinsic principal carrier, before the
separate full-H_G selected set of characters transport. -/
def principalSeed :
    Definition35IBAWBijection (D.problem reduction) (D.automorphisms reduction) flz :=
  (correctionInput D reduction E rootConvention downSupport S fixed FM L
    iotaT OT injT A laws blocks standard brough brauerExtension ordinaryExtension
    butterfly quotientInterpretation inflation flz meaning standardTransport O M
    globalRoots).definition35Seed

end ModularRep.PaperProofs.OddTwoPrincipalCorrectedSeed


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
