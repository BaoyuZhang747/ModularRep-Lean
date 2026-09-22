import ModularRep.PaperProofs.TypeBRankThreePrincipalAmbientFieldMatching
import ModularRep.PaperProofs.TypeBPrincipalRawInertiaGeometry
import ModularRep.PaperProofs.TypeBIndexTwoAmbientCommutator
import ModularRep.PaperProofs.TypeBCriterionEmbeddedPairBinding
import ModularRep.PaperProofs.TypeBCommonConjugateGlobalExtensions
import ModularRep.PaperProofs.TypeBOrthogonalAmbientOmegaBinding

/-!
# Actual principal raw-weight inertia and common SO-conjugate inertias

The same computed SO correspondence identifies the full character inertia
with the embedded Omega group times the normalizer inertia of every raw
representative of the covered Omega class. The raw inertia is contained in
that character inertia. Index two also gives the commutator bound and the
same full inertia at every SO-conjugate of the Brauer character.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise commutatorElement

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalRawInertiaBinding

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalFieldNaturality TypeBRankThreePrincipalFieldMatchingSplitting
open TypeBRankThreePrincipalMatchedInertia TypeBGreenPrincipalConstituentSource
open TypeBCliffordOrthogonalAmbientQuotient TypeBCliffordOrthogonalAmbientActionBinding
open TypeBCliffordOrthogonalFullFieldBinding NavarroCoveringBrauerExtension
open TypeBCriterionHypotheses TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open CyclicOuterLemma37Concrete TypeBSemidirectFixedFieldFactorization
open TypeBRankThreePrincipalAmbientFieldMatching

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section PrincipalSources

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] {r f : ℕ} [CharP F r]
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  {S : OmegaWeightSource (k := k) (K := K) F}
  {SH : SOWeightSource (k := k) (K := K) F}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
  {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
  {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
  {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
  {literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val}
  {indexTwo : (G F).index = 2}
  {parameters : OddFieldParameters F r f} {N : NormSource 3 F}
  {fieldSource : FieldActionSource 3 F r f parameters N}
  {C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N}
  {Msys : ModularSystem 2 K O k}
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb indexTwo)
  (roots : TypeBGreenPrincipalConstituentSource.RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  (fyz : TypeBRankThreePrincipalWeightFieldSplitting.FYZCorollary363SplittingSource
    F r f parameters Msys coefficient root rootH
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys root rootCalibration)
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys rootH rootHCalibration)
    S SH literal literalH guard guardH b hb bH hbH)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C
local notation "A" => OrthogonalAmbient 3 F parameters le_rfl N C fieldSource

/-- The generic criterion equivalence is this actual matrix Omega embedding. -/
theorem baseEquiv_eq_omegaEquiv :
    TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) matrixField =
      TypeBOrthogonalAmbientOmegaBinding.omegaEquiv fieldSource le_rfl C := rfl


include indexTwo in
/-- The commutator bound uses the literal matrix Omega, SO and field action. -/
theorem omegaBrauerInertia_commutator_le (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    ⁅brauerInertia (G F) matrixField matrixAction root theta.val, embeddedM matrixField⁆ ≤
      brauerInertia (G F) matrixField matrixAction root theta.val ⊓ embeddedM matrixField := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact TypeBIndexTwoAmbientCommutator.brauerInertia_commutator_le
    (G F) matrixField matrixAction indexTwo root theta.val

include indexTwo in
/-- Every actual SO-conjugate has the same original full ambient inertia. -/
theorem omegaBrauerInertia_all_SO_conjugates
    (theta : OmegaBrauer F root b) (h : H F) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    brauerInertia (G F) matrixField matrixAction root
        (IrreducibleBrauerCharacter.twist root theta.val
          (MulAut.conjNormal (H := G F) h⁻¹)) =
      brauerInertia (G F) matrixField matrixAction root theta.val := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact TypeBIndexTwoAmbientCommutator.brauerInertia_conjugate_eq
    (G F) matrixField matrixAction indexTwo root theta.val h

include indexTwo in
/-- All SO-conjugates extend on the original actual SO-inertia group. -/
theorem omegaBrauer_all_SO_conjugates_extend_originalM
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    ∀ h : H F, Nonempty (BrauerExtensionIn
      (G F) matrixField root
      (TypeBCommonConjugateGlobalExtensions.conjugateCharacter (G F) root theta.val h)
      (TypeBCommonConjugateGlobalExtensions.originalMInertia
        (G F) matrixField matrixAction root theta.val)) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact TypeBCommonConjugateGlobalExtensions.allMConjugates_extend_originalM
    (G F) matrixField matrixAction indexTwo root principle theta.val

include indexTwo in
/-- The original Omega-and-field-inertia group also remains fixed for every conjugate. -/
theorem omegaBrauer_all_SO_conjugates_extend_originalField
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    ∀ h : H F, Nonempty (BrauerExtensionIn
      (G F) matrixField root
      (TypeBCommonConjugateGlobalExtensions.conjugateCharacter (G F) root theta.val h)
      (TypeBCommonConjugateGlobalExtensions.originalFieldInertia
        (G F) matrixField matrixAction root theta.val)) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact TypeBCommonConjugateGlobalExtensions.allMConjugates_extend_originalField
    (G F) matrixField matrixAction indexTwo root principle theta.val

variable
  {delta : H F} {outside : delta ∉ G F} {notThree : Nat.card F ≠ 3}
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta indexTwo outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)

local notation "omegaMap" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "omegaDelta" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv_delta covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction


include gggr fyz in
/-- The same SO matching contains the inertia of every literal raw representative. -/
theorem principalSOEquiv_rawNormalizerInertia_le_brauerInertia
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val)
    (W : CharacterWeight 2 K (G F))
    (representative : TypeBSpinRawWeightSeparationBinding.classOf (G F) W = w.val) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    rawNormalizerInertia (G F) matrixField matrixAction W ≤
      brauerInertia (G F) matrixField matrixAction root theta.val := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  rw [principalSOEquiv_matched_ambient_inertia_eq gggr roots fieldScope green
    principalLift clifford principalRestriction fyz covering counts Phi theta w occurs covered]
  simpa only [representative] using
    TypeBPrincipalRawInertiaGeometry.rawNormalizerInertia_le_classInertia
      (G F) matrixField matrixAction W

include gggr fyz in
/-- The full matched character inertia is the embedded base times that very raw inertia. -/
theorem principalSOEquiv_embeddedG_mul_rawNormalizerInertia_eq_brauerInertia
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val)
    (W : CharacterWeight 2 K (G F))
    (representative : TypeBSpinRawWeightSeparationBinding.classOf (G F) W = w.val) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    (embeddedG (G F) matrixField : Set A) *
        (rawNormalizerInertia (G F) matrixField matrixAction W : Set A) =
      (brauerInertia (G F) matrixField matrixAction root theta.val : Set A) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  rw [principalSOEquiv_matched_ambient_inertia_eq gggr roots fieldScope green
    principalLift clifford principalRestriction fyz covering counts Phi theta w occurs covered]
  simpa only [representative] using
    TypeBPrincipalRawInertiaGeometry.embeddedG_mul_rawNormalizerInertia_eq_classInertia
      (G F) matrixField matrixAction W

include gggr fyz in
/-- The required inclusion for the specified pair uses the transported actual carriers. -/
theorem principalSOEquiv_U_le_T
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val)
    (W : CharacterWeight 2 K (G F))
    (representative : TypeBSpinRawWeightSeparationBinding.classOf (G F) W = w.val) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    U (embeddedG (G F) matrixField)
        (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) matrixField W) ≤
      T (embeddedG (G F) matrixField)
        (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) matrixField root)
        (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root theta.val) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  rw [← TypeBCriterionEmbeddedPairBinding.rawNormalizerInertia_eq_U
    (G F) matrixField matrixAction W,
    ← TypeBCriterionEmbeddedPairBinding.brauerInertia_eq_T
      (G F) matrixField matrixAction root theta.val]
  exact principalSOEquiv_rawNormalizerInertia_le_brauerInertia gggr roots fieldScope
    green principalLift clifford principalRestriction fyz covering counts
    Phi theta w occurs covered W representative

include gggr fyz in
/-- The manuscript's base-times-local-inertia equation on the actual embedded pair. -/
theorem principalSOEquiv_embeddedG_mul_U_eq_T
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val)
    (W : CharacterWeight 2 K (G F))
    (representative : TypeBSpinRawWeightSeparationBinding.classOf (G F) W = w.val) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    (embeddedG (G F) matrixField : Set A) *
        (U (embeddedG (G F) matrixField)
          (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) matrixField W) : Set A) =
      (T (embeddedG (G F) matrixField)
        (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) matrixField root)
        (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root theta.val) : Set A) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  rw [← TypeBCriterionEmbeddedPairBinding.rawNormalizerInertia_eq_U
    (G F) matrixField matrixAction W,
    ← TypeBCriterionEmbeddedPairBinding.brauerInertia_eq_T
      (G F) matrixField matrixAction root theta.val]
  exact principalSOEquiv_embeddedG_mul_rawNormalizerInertia_eq_brauerInertia
    gggr roots fieldScope green principalLift clifford principalRestriction fyz covering counts
    Phi theta w occurs covered W representative

end PrincipalSources

end ModularRep.PaperProofs.TypeBRankThreePrincipalRawInertiaBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
