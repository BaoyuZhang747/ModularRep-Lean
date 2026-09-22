import ModularRep.PaperProofs.OddTwoBroughToDefinition35
import ModularRep.PaperProofs.OddTwoBroughPrincipalFourClauses
import ModularRep.PaperProofs.OddTwoPrincipalDiagonalOrbitActions

/-!
# The actual Brough relation supplies the principal orbit witness

The original FM image supplies its literal selected pair and its own
quotient pair. The same joint root data are used in BS4.6, butterfly,
central inflation and Definition 3.5. The resulting conformal element
changes only the global character. Its checked two-action alternatives
give the exact disjunction used by principal orbit correction.

All mathematical source inputs are the previously licensed interfaces.
This module does not assume the disjunction or relation covariance.
The latter remains a separate join before a corrected seed can be built.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalBroughOrbitWitness

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
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoActualCentralInflationRelation
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoDefinition35TupleBinding
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness
open ModularRep.PaperProofs.OddTwoBroughCoveringSource
open ModularRep.PaperProofs.OddTwoBroughLemma46SourceAndPacket
open ModularRep.PaperProofs.OddTwoBroughPrincipalFourClauses
open ModularRep.PaperProofs.OddTwoBroughToDefinition35
open ModularRep.PaperProofs.OddTwoPrincipalDiagonalOrbitActions
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
  (LiteralDiagonalFieldRealisation)

universe u

variable {n : ℕ} {F k K Block J BlockT : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]
variable [MulAction (MulAut (PCSp n F))ᵐᵒᵖ BlockT]

local instance witnessFiniteType (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)

/-- Joint root data retain the EXACT selected quotient root. This data
record asserts no relation, extension or orbit conclusion. -/
structure SelectedPairRootData (w : D.PrincipalWeight) where
  pair : CompatiblePairReductions cover D.iota E.iotaDown (weightRepresentative D w)
  selectedCompatible : RootCompatibleAlong
    (selectedQuotientReduction D reduction w).iota pair.upRoot
    (normalizerProjection (weightRepresentative D w).subgroup)

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
variable (definitionInterpretation : Definition35TupleInterpretation D reduction flz standard)

include downSupport fixed L laws blocks brough brauerExtension ordinaryExtension
  butterfly quotientInterpretation inflation definitionInterpretation in
/-- BS4.6 now produces the conformal element and actual relation. The
ORIGINAL selected FM weight, pair reduction and quotient root stay fixed. -/
theorem exists_conformal_definition35 (psi : E.DownPrincipalBrauer)
    (globalRoots : GlobalRoots S E.iotaDown psi.1)
    (roots : SelectedPairRootData D reduction E (FM.omega (E.brauerEquiv psi))) :
    let _ := ambientBrauerAction E downSupport S
    ∃ t : PCSp n F,
      flz.definition35BlockIsomorphic
        (E.brauerEquiv ((SemidirectProduct.inl t : Ambient (n := n) (F := F)) • psi))
        (FM.omega (E.brauerEquiv psi)) := by
  dsimp only
  letI := S.normal_image
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  letI := ambientBrauerAction E downSupport S
  let w := FM.omega (E.brauerEquiv psi)
  have hUp := (selectedCharacterWeight_spec D.blockSource D.principalBlock w).symm
  have hDown : weightClass
      (OddTwoCentralTwoRelationInflation.spQuotientPair cover (weightRepresentative D w)) =
      (E.descendedFengMalleOmega FM psi).1 :=
    (E.descendedFengMalleOmega_quotientPair FM psi (weightRepresentative D w) hUp).symm
  obtain ⟨t, ht⟩ := exists_principal_brough_relation E downSupport S fixed FM L
    iotaT OT injT A laws blocks standard brough brauerExtension ordinaryExtension psi
    (OddTwoCentralTwoRelationInflation.spQuotientPair cover (weightRepresentative D w))
    hDown globalRoots (quotientOwnReduction D cover w roots.pair) roots.pair.downCompatible
  refine ⟨t, ?_⟩
  exact definition35_of_translated_brough D reduction E L S standard butterfly
    quotientInterpretation inflation flz definitionInterpretation downSupport fixed FM psi
    (SemidirectProduct.inl t) roots.pair roots.selectedCompatible ht

variable (O : LiteralDiagonalFieldRealisation n F)
variable (M : ProjectiveMultiplierSource C)

local instance witnessGammaBrauerAction : MulAction (D.problem reduction).Gamma
    D.PrincipalBrauer :=
  definition35BrauerAction (D.problem reduction)

local instance witnessDefinition35BrauerAction : MulAction (D.problem reduction).Gamma
    (Definition35Brauer (D.problem reduction)) :=
  definition35BrauerAction (D.problem reduction)

include downSupport fixed L laws blocks brough brauerExtension ordinaryExtension
  butterfly quotientInterpretation inflation definitionInterpretation M in
/-- Split the checked alternatives for the SAME conformal element supplied
by BS4.6. The weight on both sides is the original FM image. -/
theorem orbitWitness_on_inflated (psi : E.DownPrincipalBrauer)
    (globalRoots : GlobalRoots S E.iotaDown psi.1)
    (roots : SelectedPairRootData D reduction E (FM.omega (E.brauerEquiv psi))) :
    flz.definition35BlockIsomorphic (E.brauerEquiv psi) (FM.omega (E.brauerEquiv psi)) ∨
      flz.definition35BlockIsomorphic
        (diagonalGamma (D := D) (O := O) (reduction := reduction) • E.brauerEquiv psi)
        (FM.omega (E.brauerEquiv psi)) := by
  letI := ambientBrauerAction E downSupport S
  obtain ⟨t, ht⟩ := exists_conformal_definition35 D reduction E downSupport S fixed FM L
    iotaT OT injT A laws blocks standard brough brauerExtension ordinaryExtension butterfly
    quotientInterpretation inflation flz definitionInterpretation psi globalRoots roots
  rcases conformal_image_gamma_alternatives D E downSupport S L O M reduction t psi with h | h
  · exact Or.inl (h ▸ ht)
  · exact Or.inr (h ▸ ht)

include downSupport fixed L laws blocks brough brauerExtension ordinaryExtension
  butterfly quotientInterpretation inflation definitionInterpretation M in
/-- The exact orbitWitness conclusion on every member of the original
Definition 3.5 carrier. Covariance is not an input or conclusion here. -/
theorem orbitWitness
    (globalRoots : ∀ psi : E.DownPrincipalBrauer, GlobalRoots S E.iotaDown psi.1)
    (roots : ∀ w : D.PrincipalWeight, SelectedPairRootData D reduction E w)
    (psi : Definition35Brauer (D.problem reduction)) :
    flz.definition35BlockIsomorphic psi (D.definition35Equiv reduction FM psi) ∨
      flz.definition35BlockIsomorphic
        (diagonalGamma (D := D) (O := O) (reduction := reduction) • psi)
        (D.definition35Equiv reduction FM psi) := by
  obtain ⟨phi, rfl⟩ := E.brauerEquiv.surjective psi
  exact orbitWitness_on_inflated D reduction E downSupport S fixed FM L
    iotaT OT injT A laws blocks standard brough brauerExtension ordinaryExtension butterfly
    quotientInterpretation inflation flz definitionInterpretation O M phi (globalRoots phi)
    (roots (FM.omega (E.brauerEquiv phi)))

end ModularRep.PaperProofs.OddTwoPrincipalBroughOrbitWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
