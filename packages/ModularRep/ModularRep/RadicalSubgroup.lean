import ModularRep.PCore
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Radical subgroups

For a subgroup `Q ≤ G`, its normaliser is regarded as a group in its own
right.  The subgroup `Q` is `p`-radical when it is the image in `G` of the
`p`-core of that normaliser.  This is the group-theoretic part of the weight
definition; defect-zero characters and block membership are separate layers.
-/

namespace ModularRep

variable {G : Type*} [Group G]

/-- The image in `G` of the `p`-core of the normaliser of `Q`. -/
def normalizerPCore (p : ℕ) (Q : Subgroup G) : Subgroup G :=
  (pCore p (Subgroup.normalizer (Q : Set G))).map
    (Subgroup.normalizer (Q : Set G)).subtype

/-- A subgroup is `p`-radical when it equals the `p`-core of its normaliser,
viewed as a subgroup of the ambient group. -/
def IsRadicalSubgroup (p : ℕ) (Q : Subgroup G) : Prop :=
  Q = normalizerPCore p Q

/-- If the ambient `p`-core is trivial, then the trivial subgroup is
`p`-radical. -/
theorem bot_isRadicalSubgroup_of_pCore_eq_bot {p : ℕ}
    (hcore : pCore p G = ⊥) :
    IsRadicalSubgroup p (⊥ : Subgroup G) := by
  let e : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) ≃* G :=
    (MulEquiv.subgroupCongr
      (Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G)))).trans
        Subgroup.topEquiv
  have hnormalizerCore :
      pCore p (Subgroup.normalizer ((⊥ : Subgroup G) : Set G)) = ⊥ :=
    pCore_eq_bot_of_mulEquiv p e hcore
  rw [IsRadicalSubgroup]
  unfold normalizerPCore
  rw [hnormalizerCore, Subgroup.map_bot]

/-- The trivial subgroup of a simple non-`p`-group is `p`-radical. -/
theorem bot_isRadicalSubgroup_of_isSimpleGroup_of_not_isPGroup
    {p : ℕ} [IsSimpleGroup G] (hG : ¬ IsPGroup p G) :
    IsRadicalSubgroup p (⊥ : Subgroup G) :=
  bot_isRadicalSubgroup_of_pCore_eq_bot
    (pCore_eq_bot_of_isSimpleGroup_of_not_isPGroup p hG)

namespace IsRadicalSubgroup

/-- Every `p`-radical subgroup is a `p`-group. -/
theorem isPGroup {p : ℕ} {Q : Subgroup G} (hQ : IsRadicalSubgroup p Q) :
    IsPGroup p Q := by
  rw [hQ]
  exact (pCore_isPGroup p (Subgroup.normalizer (Q : Set G))).map
    (Subgroup.normalizer (Q : Set G)).subtype

/-- The defining equality, with the `p`-core displayed inside the normaliser. -/
theorem eq_normalizerPCore {p : ℕ} {Q : Subgroup G}
    (hQ : IsRadicalSubgroup p Q) :
    Q = (pCore p (Subgroup.normalizer (Q : Set G))).map
      (Subgroup.normalizer (Q : Set G)).subtype :=
  hQ

end IsRadicalSubgroup

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
