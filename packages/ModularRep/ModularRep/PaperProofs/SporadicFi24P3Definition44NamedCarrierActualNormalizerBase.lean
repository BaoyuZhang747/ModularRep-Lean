import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
import ModularRep.NormalCoreTransport

/-! The actual local base for an injective group embedding. The normalizer
equivalence and its ambient square are deductions; no normalizer-equality
source is required. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase

open ModularRep

universe u
variable {G A : Type u} [Group G] [Group A]

abbrev embeddedNormalizer (i : G →* A) (Q : Subgroup G) : Subgroup A :=
  Subgroup.normalizer (Q.map i : Set A)

abbrev embeddedLocalBase (i : G →* A) (Q : Subgroup G) :
    Subgroup (embeddedNormalizer i Q) :=
  i.range.comap (embeddedNormalizer i Q).subtype

theorem normalizer_comap_of_injective
    (i : G →* A) (hi : Function.Injective i) (Q : Subgroup G) :
    (embeddedNormalizer i Q).comap i = Subgroup.normalizer (Q : Set G) := by
  change (Subgroup.normalizer (Q.map i : Set A)).comap i = _
  rw [Subgroup.comap_normalizer_eq_of_le_range (Q.map_le_range i),
    Subgroup.comap_map_eq_self_of_injective hi Q]

def normalizerToLocalBase (i : G →* A) (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →* embeddedLocalBase i Q :=
  (ModularRep.normalizerMap i Q).codRestrict _ (by
    intro n
    exact ⟨n.1, rfl⟩)

theorem normalizerToLocalBase_bijective
    (i : G →* A) (hi : Function.Injective i) (Q : Subgroup G) :
    Function.Bijective (normalizerToLocalBase i Q) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg (fun z : embeddedLocalBase i Q => (z.1 : A)) h
  · intro y
    obtain ⟨x, hx⟩ := (show (y.1 : A) ∈ i.range from y.2)
    have hn : x ∈ Subgroup.normalizer (Q : Set G) := by
      rw [← normalizer_comap_of_injective i hi Q]
      change i x ∈ embeddedNormalizer i Q
      rw [hx]
      exact y.1.2
    refine ⟨⟨x, hn⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

def normalizerBaseEquiv
    (i : G →* A) (hi : Function.Injective i) (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≃* embeddedLocalBase i Q :=
  MulEquiv.ofBijective (normalizerToLocalBase i Q)
    (normalizerToLocalBase_bijective i hi Q)

theorem normalizerBaseEquiv_ambient
    (i : G →* A) (hi : Function.Injective i) (Q : Subgroup G)
    (n : Subgroup.normalizer (Q : Set G)) :
    ((normalizerBaseEquiv i hi Q n).1 : A) = i n.1 := rfl

theorem normalizerBaseEquiv_inclusion_square
    (i : G →* A) (hi : Function.Injective i) (Q : Subgroup G) :
    (embeddedNormalizer i Q).subtype.comp
        ((embeddedLocalBase i Q).subtype.comp (normalizerBaseEquiv i hi Q).toMonoidHom) =
      i.comp (Subgroup.normalizer (Q : Set G)).subtype := by
  ext n
  rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
