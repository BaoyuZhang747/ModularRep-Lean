import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-!
# Canonical transport to the local base group

The local base group in the ambient formulation is canonically the normaliser
of the image of the quotient radical subgroup.  This module constructs the
equivalence and its naturality from subgroup transport alone.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

open Formalisation
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- The two nested-subgroup descriptions of the local base have the same
underlying elements. -/
def ambientLocalBaseEquivIntermediateLocalBase
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    AmbientLocalBase P reference psi w quotient ambient ≃*
      IntermediateLocalNormalizer (w := w) ambient ambient.base where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Pulling the ambient radical subgroup back to the base gives the image of
the quotient radical under the fixed base equivalence. -/
theorem ambientRadical_comap_base
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    (ambientRadical P reference psi w quotient ambient).comap
        ambient.base.subtype =
      (quotientRadical P reference w).map
        ambient.baseEquiv.toMonoidHom := by
  unfold ambientRadical quotientToAmbient
  rw [← Subgroup.map_map,
    Subgroup.comap_map_eq_self_of_injective
      ambient.base.subtype_injective]

private theorem ambientRadical_le_base_range
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    ambientRadical P reference psi w quotient ambient ≤
      ambient.base.subtype.range := by
  unfold ambientRadical quotientToAmbient
  rw [← Subgroup.map_map]
  exact Subgroup.map_le_range _ _

/-- Inside the base group, normalising the transported quotient radical is
equivalent to lying in the ambient normaliser. -/
theorem quotientNormalizer_eq_intermediateLocalBase
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    Subgroup.normalizer
        ((quotientRadical P reference w).map
          ambient.baseEquiv.toMonoidHom : Set ambient.base) =
      IntermediateLocalNormalizer (w := w) ambient ambient.base := by
  unfold IntermediateLocalNormalizer AmbientLocalGroup
  rw [Subgroup.comap_normalizer_eq_of_le_range
      (ambientRadical_le_base_range ambient),
    ambientRadical_comap_base]

/-- The canonical equivalence used to regard the quotient local normaliser as
the local base subgroup of the ambient normaliser. -/
def canonicalLocalBaseEquiv
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)) ≃*
      AmbientLocalBase P reference psi w quotient ambient :=
  ((ModularRep.normalizerEquiv ambient.baseEquiv
      (quotientRadical P reference w)).trans
    (MulEquiv.subgroupCongr
      (quotientNormalizer_eq_intermediateLocalBase ambient))).trans
    (ambientLocalBaseEquivIntermediateLocalBase ambient).symm

/-- The canonical local-base equivalence is the literal ambient embedding on
underlying group elements. -/
@[simp]
theorem canonicalLocalBaseEquiv_natural
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (n : Subgroup.normalizer
      (quotientRadical P reference w :
        Set (CentralCharacterQuotient P reference))) :
    ((canonicalLocalBaseEquiv ambient n).1.1 : ambient.A) =
      quotientToAmbient P reference psi quotient ambient n.1 :=
  rfl

/-- The canonical map from the quotient group into the ambient group is
injective. -/
theorem quotientToAmbient_injective
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    Function.Injective
      (quotientToAmbient P reference psi quotient ambient) := by
  intro x y hxy
  apply ambient.baseEquiv.injective
  apply ambient.base.subtype_injective
  exact hxy

/-- The inverse canonical local-base equivalence has the expected underlying
image in the ambient group. -/
theorem canonicalLocalBaseEquiv_symm_natural
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (a : AmbientLocalBase P reference psi w quotient ambient) :
    quotientToAmbient P reference psi quotient ambient
        ((canonicalLocalBaseEquiv ambient).symm a).1 =
      a.1.1 := by
  calc
    quotientToAmbient P reference psi quotient ambient
        ((canonicalLocalBaseEquiv ambient).symm a).1 =
      (canonicalLocalBaseEquiv ambient
        ((canonicalLocalBaseEquiv ambient).symm a)).1.1 :=
      (canonicalLocalBaseEquiv_natural ambient
        ((canonicalLocalBaseEquiv ambient).symm a)).symm
    _ = a.1.1 :=
      congrArg
        (fun x : AmbientLocalBase P reference psi w quotient ambient =>
          x.1.1)
        ((canonicalLocalBaseEquiv ambient).apply_symm_apply a)

namespace IntermediateBlockSource

/-- Construct the full intermediate block source when the subgroup interval
contains only its base and top elements. -/
def ofBaseOrTop
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (baseOrTop : ∀ (J : Subgroup ambient.A), ambient.base ≤ J →
      J = ambient.base ∨ J = ⊤)
    (atBase : IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient extensions ambient.base)
    (atTop : IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient extensions (⊤ : Subgroup ambient.A)) :
    IntermediateBlockSource P reference psi w quotient weight localInflation
      ambient extensions where
  equalityAt J hJ := by
    classical
    by_cases hbase : J = ambient.base
    · subst J
      exact atBase
    · have htop : J = ⊤ := (baseOrTop J hJ).resolve_left hbase
      subst J
      exact atTop

end IntermediateBlockSource

end ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
