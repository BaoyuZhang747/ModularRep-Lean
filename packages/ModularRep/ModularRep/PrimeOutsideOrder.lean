import ModularRep.RadicalSubgroup
import Mathlib.GroupTheory.Coset.Card

/-!
# Prime subgroups outside the group order

This file isolates the elementary finite group part of the manuscript branch
in which a prime `p` does not divide the order of a finite group `G`.  It
proves that every `p`-subgroup of `G` is trivial, that `O_p(G)` is trivial,
and that the trivial subgroup is the unique `p`-radical subgroup.

No assertion about blocks, characters, extensions, or the inductive
blockwise Alperin weight condition is made here.  Those
representation theoretic steps remain separate dependencies.
-/

namespace ModularRep

variable {G : Type*} [Group G]

/-- If the prime `p` does not divide the order of `G`, every `p`-subgroup of
`G` is trivial. -/
theorem isPGroup_subgroup_eq_bot_of_not_dvd_card
    [Finite G] {p : ℕ} (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G)
    (P : Subgroup G) (hP : IsPGroup p P) : P = ⊥ := by
  let _ : Fact p.Prime := ⟨hp⟩
  rcases hP.card_eq_or_dvd with hcard | hpP
  · exact Subgroup.card_eq_one.mp hcard
  · exact (hpG (hpP.trans (Subgroup.card_subgroup_dvd_card P))).elim

/-- If the prime `p` does not divide the order of `G`, then `O_p(G)` is
trivial. -/
theorem pCore_eq_bot_of_not_dvd_card
    [Finite G] {p : ℕ} (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G) :
    pCore p G = ⊥ :=
  isPGroup_subgroup_eq_bot_of_not_dvd_card hp hpG (pCore p G)
    (pCore_isPGroup p G)

/-- Under the same coprimality hypothesis, the trivial subgroup is
`p`-radical. -/
theorem bot_isRadicalSubgroup_of_not_dvd_card
    [Finite G] {p : ℕ} (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G) :
    IsRadicalSubgroup p (⊥ : Subgroup G) := by
  rw [IsRadicalSubgroup]
  unfold normalizerPCore
  have hnormalizer :
      ¬ p ∣ Nat.card (Subgroup.normalizer ((⊥ : Subgroup G) : Set G)) := by
    simpa only [Subgroup.normalizer_eq_top, Subgroup.card_top] using hpG
  rw [pCore_eq_bot_of_not_dvd_card hp hnormalizer, Subgroup.map_bot]

/-- If `p` does not divide the order of `G`, a subgroup is `p`-radical if
and only if it is trivial. -/
theorem isRadicalSubgroup_iff_eq_bot_of_not_dvd_card
    [Finite G] {p : ℕ} (hp : p.Prime) (hpG : ¬ p ∣ Nat.card G)
    (Q : Subgroup G) : IsRadicalSubgroup p Q ↔ Q = ⊥ := by
  constructor
  · intro hQ
    exact isPGroup_subgroup_eq_bot_of_not_dvd_card hp hpG Q hQ.isPGroup
  · intro hQ
    subst Q
    exact bot_isRadicalSubgroup_of_not_dvd_card hp hpG

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
