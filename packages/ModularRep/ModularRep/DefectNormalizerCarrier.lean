import ModularRep.BlockDefectGroup
import ModularRep.CentralBrauerInterval
import ModularRep.PCore

/-!
# Defect subgroup carriers inside their normalizers

This file contains only group-theoretic carrier facts for a subgroup `P` and
its normalizer.  It identifies the copy of `P` inside `N_G(P)`, records its
normality and `p`-core containment, proves injectivity of mapping subgroups
along the normalizer subtype, and constructs the canonical central Brauer
interval with upper endpoint `N_G(P)`.

It contains no block-theoretic assertion, defect-representative, First Main,
source, or correspondence assertion.
-/

namespace ModularRep

variable {p : Nat} {G : Type*} [Group G]

/-- Mapping the copy of `P` in its normalizer back to the ambient group
recovers `P`. -/
theorem defectSubgroupInNormalizer_map_subtype (P : Subgroup G) :
    (defectSubgroupInNormalizer P).map (defectNormalizer P).subtype = P :=
  Subgroup.map_subgroupOf_eq_of_le P.le_normalizer

/-- The copy of `P` inside its normalizer is normal. -/
theorem defectSubgroupInNormalizer_normal (P : Subgroup G) :
    (defectSubgroupInNormalizer P).Normal := by
  infer_instance

/-- A `p`-subgroup is contained in the `p`-core of its normalizer when viewed
on the normalizer carrier. -/
theorem defectSubgroupInNormalizer_le_pCore {P : Subgroup G}
    (hP : IsPGroup p P) :
    defectSubgroupInNormalizer P ≤ pCore p (defectNormalizer P) := by
  let _ : (defectSubgroupInNormalizer P).Normal :=
    defectSubgroupInNormalizer_normal P
  exact normal_pSubgroup_le_pCore p _
    (defectSubgroupInNormalizer_isPGroup hP)

/-- Mapping subgroups of `N_G(P)` into the ambient group is injective. -/
theorem map_normalizerSubtype_injective {P : Subgroup G} :
    Function.Injective (fun D : Subgroup (defectNormalizer P) =>
      D.map (defectNormalizer P).subtype) :=
  Subgroup.map_injective (defectNormalizer P).subtype_injective

/-- The normalizer is the canonical upper endpoint of the central Brauer
interval `P C_G(P) ≤ H ≤ N_G(P)`. -/
noncomputable def normalizerCentralBrauerInterval
    {P : Subgroup G} (hP : IsPGroup p P) :
    CentralBrauerInterval (p := p) P (defectNormalizer P) where
  isPGroup := hP
  pCentralizer_le := sup_le P.le_normalizer
    (Subgroup.centralizer_le_normalizer (P : Set G))
  le_normalizer := le_rfl

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
