import ModularRep.PaperProofs.EvenFieldFixedQuotient
import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly

/-!
# Transport of the relative-normaliser calculation

This module formalises the passage in manuscript Lemma 3.6 from the
representative-level Weyl calculation on the standard rational Levi to the
elementwise relation on the selected finite normaliser.

The preferred source interface consists of the canonical map to the relative
Weyl quotient, identification of its kernel with the standard finite Levi,
compatibility with the standard field action, and the published pointwise
fixation of that quotient.  Lean first derives
`y⁻¹ * sigma y ∈ L` for every element of the standard fixed-point
normaliser.  Conjugation by the Lang witness is represented by compatible
group equivalences on the normaliser and on the finite Levi, together with
the manuscript's intertwining equation.  The conclusion is the exact
`relative_difference` function consumed by
`EvenFieldGenericOrbitTheoremFirst`.

No triviality of a quotient action, character fixedness, pair fixedness, or
orbit fixedness is assumed.
-/

namespace ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter

open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldFixedQuotient
open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {G N₂ : Type u} [Group G] [Group N₂]

/-- General source-shaped E8 data.  The concrete relative-Weyl construction
uses `WeylNormalizer = N_W(W_I) / W_I` and `WeylLevi = ⊥`.  Thus
`representativeMap` is the canonical map to the relative quotient, rather
than a nonexistent canonical lift to `N_W(W_I)`.  The more general inverse
image formulation is retained for compatibility with existing callers.

Compatibility transports the standard field action to the chosen target,
and `fieldAction_fixed` is the published fact that the standard field
endomorphism acts trivially there.  In the concrete quotient instantiation,
`base_eq_comap` is exactly the assertion that the kernel is the standard
finite Levi.

This interface states no triviality result on either the standard relative
quotient or the selected finite-normaliser quotient. -/
structure WeylRepresentativeData
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer) where
  representativeMap : N →* WeylNormalizer
  fieldAction : MulAut WeylNormalizer
  compatible : ∀ y : N,
    representativeMap
        (restrictToStableSubgroup N
          (frobeniusFixedSubgroupHom F sigma commute) N_stable y) =
      fieldAction (representativeMap y)
  fieldAction_fixed : ∀ w : WeylNormalizer, fieldAction w = w
  base_eq_comap : fixedBase F N L = WeylLevi.comap representativeMap

/-- Source data for the concrete E8 target
`Q = N_W(W_I) / W_I`.  The denominator has already been divided out, so the
distinguished subgroup of `Q` is bottom.  The only structural identification
required here is the kernel equality for the canonical relative-quotient
map. -/
structure RelativeWeylQuotientData
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (Q : Type u) [Group Q] where
  quotientMap : N →* Q
  fieldAction : MulAut Q
  compatible : ∀ y : N,
    quotientMap
        (restrictToStableSubgroup N
          (frobeniusFixedSubgroupHom F sigma commute) N_stable y) =
      fieldAction (quotientMap y)
  fieldAction_fixed : ∀ q : Q, fieldAction q = q
  base_eq_ker : fixedBase F N L = quotientMap.ker

/-- Regard concrete relative-quotient data as the general E8 interface, with
the denominator represented by the bottom subgroup of the quotient. -/
def RelativeWeylQuotientData.toWeylRepresentativeData
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (Q : Type u) [Group Q]
    (D : RelativeWeylQuotientData F sigma commute N N_stable L Q) :
    WeylRepresentativeData F sigma commute N N_stable L Q ⊥ where
  representativeMap := D.quotientMap
  fieldAction := D.fieldAction
  compatible := D.compatible
  fieldAction_fixed := D.fieldAction_fixed
  base_eq_comap := by
    rw [D.base_eq_ker]
    ext y
    simp

/-- E8's structural relative-Weyl data imply the representative relation in
the standard finite normaliser. -/
theorem standardDifference_mem_of_weylData
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData F sigma commute N N_stable L
      WeylNormalizer WeylLevi) :
    ∀ y : N,
      y⁻¹ *
          restrictToStableSubgroup N
            (frobeniusFixedSubgroupHom F sigma commute) N_stable y ∈
        fixedBase F N L := by
  intro y
  rw [weyl.base_eq_comap]
  change weyl.representativeMap
      (y⁻¹ *
        restrictToStableSubgroup N
          (frobeniusFixedSubgroupHom F sigma commute) N_stable y) ∈ WeylLevi
  rw [map_mul, map_inv, weyl.compatible, weyl.fieldAction_fixed]
  simp

/-- The concrete relative-Weyl quotient data imply the representative
relation in the standard finite normaliser.  This is the E8 helper intended
for the manuscript instantiation. -/
theorem standardDifference_mem_of_relativeWeylQuotientData
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (Q : Type u) [Group Q]
    (quotient : RelativeWeylQuotientData F sigma commute N N_stable L Q) :
    ∀ y : N,
      y⁻¹ *
          restrictToStableSubgroup N
            (frobeniusFixedSubgroupHom F sigma commute) N_stable y ∈
        fixedBase F N L :=
  standardDifference_mem_of_weylData F sigma commute N N_stable L Q ⊥
    (quotient.toWeylRepresentativeData F sigma commute N N_stable L Q)

/-- The two restrictions of conjugation by the Lang witness: one on the
standard fixed-point normaliser and one on the standard finite Levi.  The
commuting square states that the latter is the restriction of the former.

In the manuscript, `normalizerEquiv` is conjugation by `g` from
`N_Hbar(L_I)^F_w` to `N_H(M)`, while `baseEquiv` is its restriction from
`L_I^F_w` to `M^F'`. -/
structure RationalLeviNormalizerTransport
    (F : G →* G) (N : Subgroup (frobeniusFixedSubgroup F))
    (L : Subgroup G) (Target : Type u) [Group Target]
    (B : Subgroup Target) where
  normalizerEquiv : N ≃* Target
  baseEquiv : fixedBase F N L ≃* B
  extendsBase : ∀ x : fixedBase F N L,
    normalizerEquiv (x : N) = ((baseEquiv x : B) : Target)

/-- Representative-level Weyl data and the rational-Levi conjugation
equivalence imply the required elementwise relation in the selected finite
normaliser.  The fact that the standard difference lies in the fixed-point
Levi is proved rather than assumed: its ambient-Levi membership is the Weyl
input, and its fixed-point membership follows because it is already an
element of the standard fixed-point normaliser. -/
private theorem relativeDifference_of_weylRepresentative
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (weylDifference : ∀ y : N,
      ((y : frobeniusFixedSubgroup F) : G)⁻¹ *
          sigma ((y : frobeniusFixedSubgroup F) : G) ∈ L)
    (B : Subgroup N₂)
    (transport : RationalLeviNormalizerTransport F N L N₂ B)
    (alpha : MulAut N₂)
    (intertwines : ∀ y : N,
      transport.normalizerEquiv
          (restrictToStableSubgroup N
            (frobeniusFixedSubgroupHom F sigma commute) N_stable y) =
        alpha (transport.normalizerEquiv y)) :
    ∀ x : N₂, x⁻¹ * alpha x ∈ B := by
  intro x
  let alphaStandard : N →* N :=
    restrictToStableSubgroup N
      (frobeniusFixedSubgroupHom F sigma commute) N_stable
  let y : N := transport.normalizerEquiv.symm x
  have standardDifference_mem : y⁻¹ * alphaStandard y ∈ fixedBase F N L := by
    change
      (((y : N) : frobeniusFixedSubgroup F) : G)⁻¹ *
          sigma (((y : N) : frobeniusFixedSubgroup F) : G) ∈ L
    exact weylDifference y
  let d : fixedBase F N L :=
    ⟨y⁻¹ * alphaStandard y, standardDifference_mem⟩
  have transportedDifference_mem :
      transport.normalizerEquiv (y⁻¹ * alphaStandard y) ∈ B := by
    change transport.normalizerEquiv (d : N) ∈ B
    rw [transport.extendsBase d]
    exact (transport.baseEquiv d).property
  have hy : transport.normalizerEquiv y = x :=
    transport.normalizerEquiv.apply_symm_apply x
  have hintertwines :
      transport.normalizerEquiv (alphaStandard y) =
        alpha (transport.normalizerEquiv y) :=
    intertwines y
  rw [map_mul, map_inv, hintertwines, hy] at transportedDifference_mem
  exact transportedDifference_mem

/-- Preferred E8 adapter.  It derives the standard representative relation
from the structural relative-Weyl data and only then transports it along the
rational-Levi conjugation equivalence. -/
theorem relativeDifference_of_weylData
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData F sigma commute N N_stable L
      WeylNormalizer WeylLevi)
    (B : Subgroup N₂)
    (transport : RationalLeviNormalizerTransport F N L N₂ B)
    (alpha : MulAut N₂)
    (intertwines : ∀ y : N,
      transport.normalizerEquiv
          (restrictToStableSubgroup N
            (frobeniusFixedSubgroupHom F sigma commute) N_stable y) =
        alpha (transport.normalizerEquiv y)) :
    ∀ x : N₂, x⁻¹ * alpha x ∈ B := by
  apply relativeDifference_of_weylRepresentative F sigma commute N N_stable L
    _ B transport alpha intertwines
  intro y
  have hy := standardDifference_mem_of_weylData F sigma commute N N_stable L
    WeylNormalizer WeylLevi weyl y
  exact hy

variable {H A : Type u} [Group H] [MulAction (MulAut H) A]

/-- Exact generic-orbit adapter using the preferred structural E8 interface,
rather than taking the representative difference relation as an input. -/
theorem relativeDifference_for_genericOrbit_of_weylData
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData F sigma commute N N_stable L
      WeylNormalizer WeylLevi)
    (tau : MulAut H) (T : A)
    (B : Subgroup (finiteNormalizer (H := H) (A := A) T))
    (transport : RationalLeviNormalizerTransport F N L
      (finiteNormalizer (H := H) (A := A) T) B)
    (intertwines : ∀ (label_fixed : tau • T = T) (y : N),
      transport.normalizerEquiv
          (restrictToStableSubgroup N
            (frobeniusFixedSubgroupHom F sigma commute) N_stable y) =
        inducedFiniteNormalizerAut tau T label_fixed
          (transport.normalizerEquiv y)) :
    ∀ (label_fixed : tau • T = T)
      (x : finiteNormalizer (H := H) (A := A) T),
      x⁻¹ * inducedFiniteNormalizerAut tau T label_fixed x ∈ B := by
  intro label_fixed
  exact relativeDifference_of_weylData F sigma commute N N_stable L
    WeylNormalizer WeylLevi weyl B transport
    (inducedFiniteNormalizerAut tau T label_fixed)
    (intertwines label_fixed)

end ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
