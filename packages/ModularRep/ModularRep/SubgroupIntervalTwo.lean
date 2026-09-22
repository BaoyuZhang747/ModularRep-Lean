import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Subgroup intervals with quotient of order at most two

If a normal subgroup has quotient of order at most two, there is no proper
intermediate subgroup.
-/

namespace ModularRep

universe u

variable {A : Type u} [Group A] [Finite A]

/-- A normal subgroup whose quotient has cardinality at most two is either
an intermediate subgroup itself or is contained in no proper intermediate
subgroup. -/
theorem subgroup_eq_base_or_top_of_quotient_card_le_two
    (N : Subgroup A) [N.Normal]
    (hcard : Nat.card (A ⧸ N) ≤ 2)
    (J : Subgroup A) (hNJ : N ≤ J) :
    J = N ∨ J = ⊤ := by
  let e := QuotientGroup.comapMk'OrderIso N
  let H : Subgroup (A ⧸ N) := e.symm ⟨J, hNJ⟩
  have hH : H = ⊥ ∨ H = ⊤ := by
    have hpos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
    have hcases : Nat.card (A ⧸ N) = 1 ∨ Nat.card (A ⧸ N) = 2 := by
      omega
    rcases hcases with hcardOne | hcardTwo
    · let _ : Subsingleton (A ⧸ N) :=
        (Nat.card_eq_one_iff_unique.mp hcardOne).1
      right
      exact (Subgroup.eq_top_iff' H).2 fun x => by
        simpa only [Subsingleton.elim x 1] using H.one_mem
    · let _ : Fact (Nat.card (A ⧸ N)).Prime := ⟨by
        simpa only [hcardTwo] using Nat.prime_two⟩
      exact H.eq_bot_or_eq_top_of_prime_card
  rcases hH with hbot | htop
  · left
    have hpair : e (⊥ : Subgroup (A ⧸ N)) = ⟨J, hNJ⟩ := by
      rw [← hbot]
      exact e.apply_symm_apply ⟨J, hNJ⟩
    have hvalue := congrArg Subtype.val hpair
    change Subgroup.comap (QuotientGroup.mk' N)
      (⊥ : Subgroup (A ⧸ N)) = J at hvalue
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hvalue
    exact hvalue.symm
  · right
    have hpair : e (⊤ : Subgroup (A ⧸ N)) = ⟨J, hNJ⟩ := by
      rw [← htop]
      exact e.apply_symm_apply ⟨J, hNJ⟩
    have hvalue := congrArg Subtype.val hpair
    change Subgroup.comap (QuotientGroup.mk' N)
      (⊤ : Subgroup (A ⧸ N)) = J at hvalue
    rw [Subgroup.comap_top] at hvalue
    exact hvalue.symm

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
