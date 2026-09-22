import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Sylow

/-!
# Cyclic Sylow subgroups from order data

A cyclic subgroup whose order contains the full `p`-part of the ambient
finite group contains a Sylow `p`-subgroup.  Consequently every `p`-subgroup
of the ambient group is cyclic.  No block theory is used here.
-/

namespace ModularRep.CyclicSylow

/-- The full `p`-part of `a * b` divides `b` when `p` does not divide the
nonzero factor `a`. -/
theorem ordProj_mul_dvd_right_of_not_dvd_left
    {p a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hpa : ¬p ∣ a) :
    ordProj[p] (a * b) ∣ b := by
  rw [Nat.ordProj_mul p ha hb,
    show ordProj[p] a = 1 by
      simp [Nat.factorization_eq_zero_of_not_dvd hpa], one_mul]
  exact Nat.ordProj_dvd b p

/-- If a cyclic subgroup contains the full `p`-part of a finite group's
order, then the ambient group has a cyclic Sylow `p`-subgroup. -/
theorem exists_cyclic_sylow_of_full_part_dvd_card_cyclic_subgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Subgroup G) [IsCyclic T]
    (hfull : p ^ (Nat.card G).factorization p ∣ Nat.card T) :
    ∃ P : Sylow p G, IsCyclic P := by
  obtain ⟨Q, hQ⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := T) p hfull
  let K : Subgroup G := Q.map T.subtype
  let e : Q ≃* K :=
    Q.equivMapOfInjective T.subtype T.subtype_injective
  have hK : Nat.card K = p ^ (Nat.card G).factorization p := by
    exact (Nat.card_congr e.toEquiv).symm.trans hQ
  let P : Sylow p G := Sylow.ofCard K hK
  refine ⟨P, ?_⟩
  change IsCyclic K
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

/-- Under the same full-part hypothesis, every `p`-subgroup is cyclic. -/
theorem isCyclic_of_isPGroup_of_full_part_dvd_card_cyclic_subgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Subgroup G) [IsCyclic T]
    (hfull : p ^ (Nat.card G).factorization p ∣ Nat.card T)
    (D : Subgroup G) (hD : IsPGroup p D) : IsCyclic D := by
  obtain ⟨P₀, hP₀⟩ :=
    exists_cyclic_sylow_of_full_part_dvd_card_cyclic_subgroup T hfull
  let _ : IsCyclic P₀ := hP₀
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  let _ : IsCyclic P :=
    isCyclic_of_surjective (Sylow.equiv P₀ P).toMonoidHom
      (Sylow.equiv P₀ P).surjective
  exact Subgroup.isCyclic_of_le hDP

end ModularRep.CyclicSylow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
