import ModularRep.PaperProofs.TypeBMatrixAmbientOrdinaryRoots
import ModularRep.PaperProofs.TypeBCriterionEmbeddedPairBinding

/-!
# The two ordinary local extensions on the actual rank-three pair

Both extensions use the same raw weight and its own ordinary quotient
character. Their groups are the original raw inertia intersected with SO
and with Omega together with the field group. Sufficient roots come from
the full actual ambient, and the only character-theoretic source is the
existing general finite group cyclic extension theorem.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalLocalExtensions

open ModularRep TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBCliffordOrthogonalAmbientQuotient TypeBCriterionHypotheses
open TypeBRankThreePrincipalMatchedInertia TypeBMatrixAmbientOrdinaryRoots
open TypeBCentralKernelInertia

variable {r f : ℕ} {F K : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  (parameters : OddFieldParameters F r f)
  (N : NormSource 3 F)
  (fieldSource : FieldActionSource 3 F r f parameters N)
  (C : TypeBCliffordOrthogonalSourceBinding.Source
    3 F r f parameters (Nat.le_refl 3) N)
  [NeZero f]

local notation "matrixField" =>
  soFieldAction 3 F parameters (Nat.le_refl 3) N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C

/-- The original SO-side inertia of this raw weight. -/
abbrev MInertia (W : CharacterWeight 2 K (omegaSubgroup 3 F)) :
    Subgroup (MatrixAmbient parameters N fieldSource C) :=
  rawNormalizerInertia (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField matrixAction W ⊓
    embeddedM matrixField

/-- The original Omega-and-field-side inertia of the same raw weight. -/
abbrev GEInertia (W : CharacterWeight 2 K (omegaSubgroup 3 F)) :
    Subgroup (MatrixAmbient parameters N fieldSource C) :=
  rawNormalizerInertia (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField matrixAction W ⊓
    baseFieldGroup (omegaSubgroup 3 F) matrixField

/-- The SO-side target uses the literal embedded raw inertia U. -/
theorem MInertia_eq_U (W : CharacterWeight 2 K (omegaSubgroup 3 F)) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (omegaSubgroup 3 F) matrixField matrixAction
    MInertia (K := K) parameters N fieldSource C W =
      U (embeddedG (omegaSubgroup 3 F) matrixField)
          (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
            (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W) ⊓
        embeddedM matrixField := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (omegaSubgroup 3 F) matrixField matrixAction
  exact congrArg (fun I : Subgroup (MatrixAmbient parameters N fieldSource C) =>
    I ⊓ embeddedM matrixField)
    (TypeBCriterionEmbeddedPairBinding.rawNormalizerInertia_eq_U
      (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField matrixAction W)

/-- The second target retains the whole original Omega-and-field factor. -/
theorem GEInertia_eq_U (W : CharacterWeight 2 K (omegaSubgroup 3 F)) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (omegaSubgroup 3 F) matrixField matrixAction
    GEInertia (K := K) parameters N fieldSource C W =
      U (embeddedG (omegaSubgroup 3 F) matrixField)
          (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
            (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W) ⊓
        baseFieldGroup (omegaSubgroup 3 F) matrixField := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (omegaSubgroup 3 F) matrixField matrixAction
  exact congrArg (fun I : Subgroup (MatrixAmbient parameters N fieldSource C) =>
    I ⊓ baseFieldGroup (omegaSubgroup 3 F) matrixField)
    (TypeBCriterionEmbeddedPairBinding.rawNormalizerInertia_eq_U
      (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField matrixAction W)

/-- The radical used in both extension quotients is the specified pair's image. -/
theorem embeddedRadical_eq (W : CharacterWeight 2 K (omegaSubgroup 3 F)) :
    (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
      (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W).subgroup.map
        (embeddedG (omegaSubgroup 3 F) matrixField).subtype =
      embeddedRadical (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W :=
  TypeBCriterionEmbeddedPairBinding.rawWeightEquiv_embeddedRadical
    (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W

/-- The specified pair retains this very ordinary character on normalizer elements. -/
theorem embeddedLocalCharacter_value
    (W : CharacterWeight 2 K (omegaSubgroup 3 F))
    (x : Subgroup.normalizer (W.subgroup : Set (omegaSubgroup 3 F)))
    (y : Subgroup.normalizer
      ((TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
        (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W).subgroup :
        Set (embeddedG (omegaSubgroup 3 F) matrixField)))
    (hxy : TypeBCriterionEmbeddedPairBinding.baseEquiv (omegaSubgroup 3 F) matrixField x = y) :
    (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
      (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W).localCharacter
        (TypeBCentralKernelWeightTransport.localMk
          (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
            (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W).subgroup y) =
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup x) :=
  TypeBCriterionEmbeddedPairBinding.rawWeightEquiv_localCharacter
    (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W x y hxy

variable [ambientRoots :
  HasEnoughRootsOfUnity K (Nat.card (MatrixAmbient parameters N fieldSource C))]

include ambientRoots in
/-- The actual SO-side cyclic quotient supplies the first ordinary extension. -/
theorem ordinary_M (W : CharacterWeight 2 K (omegaSubgroup 3 F))
    (ordinarySource : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)],
        TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K H)
    (indexTwo : (omegaSubgroup 3 F).index = 2) :
    Nonempty (LocalOrdinaryExtension (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W
      (MInertia (K := K) parameters N fieldSource C W)) := by
  letI := mInertiaOrdinaryRoots parameters N fieldSource C W
  exact TypeBLocalOrdinaryExtensionSplitting.ordinary_M
    (omegaSubgroup 3 F) matrixField matrixAction W
    (ordinarySource (MInertiaQuotient parameters N fieldSource C W))
    (omegaQuotient_isCyclic indexTwo)

include ambientRoots in
/-- The original Omega-and-field quotient supplies the second extension. -/
theorem ordinary_GE (W : CharacterWeight 2 K (omegaSubgroup 3 F))
    (ordinarySource : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)],
        TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K H) :
    Nonempty (LocalOrdinaryExtension (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W
      (GEInertia (K := K) parameters N fieldSource C W)) := by
  letI := geInertiaOrdinaryRoots parameters N fieldSource C W
  exact TypeBLocalOrdinaryExtensionSplitting.ordinary_GE
    (omegaSubgroup 3 F) matrixField matrixAction W
    (ordinarySource (GEInertiaQuotient parameters N fieldSource C W))

include ambientRoots in
/-- Both ordinary antecedents on the same raw weight and original groups. -/
theorem ordinary_extensions (W : CharacterWeight 2 K (omegaSubgroup 3 F))
    (ordinarySource : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)],
        TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K H)
    (indexTwo : (omegaSubgroup 3 F).index = 2) :
    Nonempty (LocalOrdinaryExtension (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W
      (MInertia (K := K) parameters N fieldSource C W)) ∧
    Nonempty (LocalOrdinaryExtension (ell := 2) (K := K) (omegaSubgroup 3 F) matrixField W
      (GEInertia (K := K) parameters N fieldSource C W)) :=
  ⟨ordinary_M parameters N fieldSource C W ordinarySource indexTwo,
    ordinary_GE parameters N fieldSource C W ordinarySource⟩

end ModularRep.PaperProofs.TypeBRankThreePrincipalLocalExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
