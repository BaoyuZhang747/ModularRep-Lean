import ModularRep.CentralClassSumExpansion
import ModularRep.GroupAlgebraCentralBrauerMapTo

/-!
# Conjugacy class sums through central Brauer maps

This file computes the public interval-valued central Brauer map on one
unnormalised global conjugacy class sum, then identifies its normalizer image
with a local conjugacy class sum under a literal centralizer-intersection
hypothesis.  Both results are generic K carrier theorems.  They contain no
block, source, induction, correspondence, or First Main assertion.
-/

namespace ModularRep

open MonoidAlgebra
open scoped BigOperators

noncomputable section

variable {p : Nat} {k G : Type*}
variable [CommSemiring k] [Group G] [Fintype G]
variable [Fact p.Prime] [CharP k p]
variable {P H : Subgroup G}

local instance normalizerClassSumsPropDecidable (Q : Prop) : Decidable Q :=
  Classical.propDecidable Q

local instance normalizerClassSumsSubgroupFintype : Fintype H :=
  Fintype.ofFinite H

/-- Coefficients of the interval-valued central Brauer image of one global
conjugacy class sum. -/
theorem centralBrauerMapTo_conjugacyClassSum_coeff
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (g : G) (x : H) :
    ((centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN
        (conjugacyClassSum (k := k) g) :
        GroupAlgebraCenter k H) : k[H]).coeff x =
      if ((x : G) ∈ centralizerOf P ∧
          (x : G) ∈ (ConjClasses.mk g).carrier) then 1 else 0 := by
  classical
  rw [centralBrauerMapTo_apply]
  change
    Finsupp.mapDomain (Subgroup.inclusion hCH)
      (MonoidAlgebra.coeff
        ((centralBrauerMap (k := k) (p := p) P hP
            (conjugacyClassSum (k := k) g) :
            GroupAlgebraCenter k (centralizerOf P)) :
          k[centralizerOf P])) x = _
  by_cases hx : (x : G) ∈ centralizerOf P
  · let c : centralizerOf P := ⟨(x : G), hx⟩
    have hinc : Subgroup.inclusion hCH c = x := Subtype.ext rfl
    rw [← hinc,
      Finsupp.mapDomain_apply (Subgroup.inclusion_injective hCH)]
    rw [centralBrauerMap_apply, centralBrauerRestriction_coeff,
      conjugacyClassSum_coeff]
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  · have hrange : x ∉ Set.range (Subgroup.inclusion hCH) := by
      rintro ⟨c, rfl⟩
      exact hx c.property
    rw [Finsupp.mapDomain_of_notMem_range _ _ hrange]
    simp [hx]

/-- A literal global-class/centralizer intersection sends the global class
sum to the corresponding normalizer class sum. -/
theorem normalizerCentralBrauerMap_conjugacyClassSum_eq_of_intersection
    (P : Subgroup G) (hP : IsPGroup p P)
    (g : G) (ell : Subgroup.normalizer (P : Set G))
    (hinter :
      ∀ x : Subgroup.normalizer (P : Set G),
        x ∈ (ConjClasses.mk ell).carrier ↔
          ((x : G) ∈ (ConjClasses.mk g).carrier ∧
            (x : G) ∈ centralizerOf P)) :
    normalizerCentralBrauerMap (k := k) (p := p) P hP
        (conjugacyClassSum (k := k) g) =
      conjugacyClassSum (k := k) ell := by
  classical
  apply Subtype.ext
  ext x
  have hcoeff :=
    centralBrauerMapTo_conjugacyClassSum_coeff
      (k := k) (p := p) P
      (Subgroup.normalizer (P : Set G)) hP
      (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl g x
  have hx :
      ((x : G) ∈ centralizerOf P ∧
        (x : G) ∈ (ConjClasses.mk g).carrier) ↔
        ConjClasses.mk x = ConjClasses.mk ell := by
    calc
      _ ↔ ((x : G) ∈ (ConjClasses.mk g).carrier ∧
            (x : G) ∈ centralizerOf P) := and_comm
      _ ↔ x ∈ (ConjClasses.mk ell).carrier := (hinter x).symm
      _ ↔ ConjClasses.mk x = ConjClasses.mk ell :=
        ConjClasses.mem_carrier_iff_mk_eq
  simp only [normalizerCentralBrauerMap]
  rw [hcoeff, conjugacyClassSum_coeff]
  by_cases hleft :
      (x : G) ∈ centralizerOf P ∧
        (x : G) ∈ (ConjClasses.mk g).carrier
  · rw [if_pos hleft, if_pos (hx.mp hleft)]
  · have hright : ¬ConjClasses.mk x = ConjClasses.mk ell :=
      fun h ↦ hleft (hx.mpr h)
    rw [if_neg hleft, if_neg hright]

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
