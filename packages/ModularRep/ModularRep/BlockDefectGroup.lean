import Mathlib.GroupTheory.PGroup
import ModularRep.SubgroupSubconjugacy

/-!
# Generic maximal nonzero p-support

This file isolates the elementary group-theoretic content of a defect-group
interface.  The predicate being supported is completely abstract: no block,
character, group algebra, or induction notion occurs here.
-/

namespace ModularRep

/-- The normalizer of an ambient subgroup, with its carrier kept explicit. -/
abbrev defectNormalizer {G : Type*} [Group G] (P : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (P : Set G)

/-- An ambient subgroup regarded as a subgroup of its own normalizer. -/
abbrev defectSubgroupInNormalizer {G : Type*} [Group G]
    (P : Subgroup G) : Subgroup (defectNormalizer P) :=
  P.subgroupOf (defectNormalizer P)

/-- Passing a p-subgroup to its normalizer carrier preserves the p-group
property. -/
theorem defectSubgroupInNormalizer_isPGroup
    {p : Nat} {G : Type*} [Group G] {P : Subgroup G}
    (hP : IsPGroup p P) :
    IsPGroup p (defectSubgroupInNormalizer P) := by
  change IsPGroup p (P.comap (defectNormalizer P).subtype)
  exact hP.comap_subtype

/-- `D` is a maximal p-subgroup, by literal inclusion, among the subgroups
where `nonzero` holds. -/
structure IsMaximalNonzeroPSubgroup
    {G : Type*} [Group G]
    (p : Nat) (nonzero : Subgroup G → Prop) (D : Subgroup G) : Prop where
  isPGroup : IsPGroup p D
  nonzero_at_D : nonzero D
  eq_of_nonzero_le :
    ∀ Q : Subgroup G, IsPGroup p Q → nonzero Q → D ≤ Q → D = Q

/-- A subconjugacy characterization of nonzero p-support makes its nominated
p-subgroup maximal by literal inclusion. -/
theorem IsMaximalNonzeroPSubgroup.of_nonzero_iff_isSubconjugate
    {G : Type*} [Group G] [Finite G]
    {p : Nat} {nonzero : Subgroup G → Prop} {D : Subgroup G}
    (hD : IsPGroup p D)
    (hiff : ∀ Q : Subgroup G, IsPGroup p Q →
      (nonzero Q ↔ Q.IsSubconjugate D)) :
    IsMaximalNonzeroPSubgroup p nonzero D := by
  refine ⟨hD, ?_, ?_⟩
  · exact (hiff D hD).mpr (Subgroup.IsSubconjugate.refl D)
  · intro Q hQ hQnonzero hDQ
    have hQD : Q.IsSubconjugate D := (hiff Q hQ).mp hQnonzero
    exact hQD.eq_of_le hDQ

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
