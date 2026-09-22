import ModularRep.PaperProofs.TypeBRankThreePrincipalBSGlobalAntecedents
import ModularRep.PaperProofs.TypeBRankThreePrincipalSOMatchingSplitting

/-!
# The selected conjugate on the same principal lower carrier

The inverse SO actor in the initial pair is the existing supported Brauer
step. Literal restriction occurrence fixes the same upper character, and
the current calibrated SO correspondence fixes the same lower seed orbit.
No orbit orientation or block-triple witness is selected in this file.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalConjugateCarrierBinding

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCriterionHypotheses TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalOrbitBinding TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBCliffordOrthogonalAmbientQuotient TypeBRankThreePrincipalMatchedInertia
open TypeBGreenPrincipalConstituentSource TypeBLocalReductionInstantiation
open TypeBFixedRootDefinitionFamily

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Embedded

variable (F : Type) [Field F] [Finite F]
  {K k : Type} [Field K] [CharZero K] [Field k] [CharP k 2] [IsAlgClosed k]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)

/-- The principal step already uses the inverse conjugation convention. -/
theorem brauerStep_val (m : H F) (theta : OmegaBrauer F root b) :
    (brauerStep F S literal root b hb m theta).val =
      IrreducibleBrauerCharacter.twist root theta.val (MulAut.conjNormal (H := G F) m⁻¹) := rfl

variable {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (fieldSource : FieldActionSource 3 F r f parameters N)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C
local notation "Ghat" => embeddedG (G F) matrixField
local notation "rootHat" => TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) matrixField root

/-- Equality on the exact character used by the initial pair permits
simultaneous dependent transport of its inclusion, catalogues and witness. -/
theorem embedded_brauerStep (theta : OmegaBrauer F root b) (m : H F) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root
        (brauerStep F S literal root b hb m theta).val =
      IrreducibleBrauerCharacter.twist rootHat
        (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root theta.val)
        (MulAut.conjNormal (H := Ghat)
          ((SemidirectProduct.inl (φ := matrixField) m)⁻¹)) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  exact TypeBRankThreePrincipalBSGlobalAntecedents.embedded_conjugate_eq
    (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) theta m

end Embedded

section SameCorrespondence
variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {r f : ℕ} [CharP F r]
  {S : OmegaWeightSource (k := k) (K := K) F}
  {SH : SOWeightSource (k := k) (K := K) F}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
  {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
  {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
  {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
  {literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val}
  {delta : H F} {indexTwo : (G F).index = 2} {outside : delta ∉ G F}
  {parameters : OddFieldParameters F r f} {notThree : Nat.card F ≠ 3}
  {Msys : ModularSystem 2 K O k}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta indexTwo outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)
  (roots : TypeBGreenPrincipalConstituentSource.RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

local notation "seed" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv
    covering counts roots fieldScope green principalLift clifford principalRestriction

/-- The selected conjugate stays above the same Phi and in the orbit of
the original calibrated seed preimage of w. Pointwise orientation is not asserted. -/
theorem principalSOEquiv_conjugateOrbit
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b)
    (w : OmegaWeight F S b)
    (occurs : NavarroCoveringBrauerExtension.BrauerOccursInRestriction
      (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val)
    (m : H F) :
    NavarroCoveringBrauerExtension.BrauerOccursInRestriction
        (G F) rootH root Phi.val (brauerStep F S literal root b hb m theta).val ∧
      soMap Phi = covering.cover (seed (brauerStep F S literal root b hb m theta)) ∧
      principalBrauerOrbitRel F S literal root b hb
        ((seed).symm w) (brauerStep F S literal root b hb m theta) := by
  have occursM := occurs_brauerStep F S literal root b hb rootH m Phi.val theta occurs
  have occursSeed : NavarroCoveringBrauerExtension.BrauerOccursInRestriction
      (G F) rootH root Phi.val ((seed).symm w).val := by
    apply (TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv_occurs_iff_coversClass
      covering counts roots fieldScope green principalLift clifford principalRestriction
      Phi ((seed).symm w)).mpr
    simpa only [Equiv.apply_symm_apply] using covered
  have aboveSeed := principalAbove_eq F root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift ((seed).symm w) Phi occursSeed
  have aboveConjugate := principalAbove_eq F root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift (brauerStep F S literal root b hb m theta) Phi occursM
  have sameOrbit :=
    (principalAbove_eq_iff F S literal root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift clifford ((seed).symm w)
      (brauerStep F S literal root b hb m theta)).mp (aboveSeed.trans aboveConjugate.symm)
  refine ⟨occursM, ?_, ?_⟩
  · exact (TypeBRankThreePrincipalSOMatchingSplitting.occurs_iff_principalSOEquiv_eq
      covering counts roots fieldScope green principalLift clifford principalRestriction
      Phi (brauerStep F S literal root b hb m theta)).mp occursM
  · exact (principalBrauerOrbitRel_iff F S literal root b hb
      ((seed).symm w) (brauerStep F S literal root b hb m theta)).mpr sameOrbit

end SameCorrespondence

end ModularRep.PaperProofs.TypeBRankThreePrincipalConjugateCarrierBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
