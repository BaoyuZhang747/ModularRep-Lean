import ModularRep.CyclicSylow
import Mathlib.Tactic

/-!
# The rank-two symplectic order and torus deduction

This file kernel checks the elementary part of Proposition 3.5 in the
accompanying manuscript.  From the factored order of `Sp₄(q)` and the
existence of a cyclic subgroup of order `q² + 1`, it proves that every
relevant `ell`-subgroup is cyclic.

The concrete group order and cyclic torus are inputs.  The file does not
construct the symplectic group, identify the universal cover, define block
defect groups, or invoke the cyclic-defect iBAW theorem.
-/

namespace ModularRep.ManuscriptVerification.RankTwoSymplectic

open ModularRep.CyclicSylow

/-- A prime different from the base prime does not divide a power of that
base. -/
theorem prime_not_dvd_prime_power_of_ne
    {ell p f : ℕ} (hell : ell.Prime) (hp : p.Prime) (hne : ell ≠ p) :
    ¬ell ∣ p ^ f := by
  intro h
  exact hne (Nat.prime_eq_prime_of_dvd_pow hell hp h)

/-- Factorisation of the standard order-formula factor `q^4 - 1`. -/
theorem pow_four_sub_one_eq_sq_sub_one_mul_sq_add_one
    {q : ℕ} (hq : 1 ≤ q) :
    q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hqpos
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow 4 q hqpos
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4]
  ring

/-- Rewrites the usual `Sp₄(q)` order formula into the factorisation used by
the full-part argument. -/
theorem sp4_order_formula_factorization {q : ℕ} (hq : 1 ≤ q) :
    q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) =
      q ^ 4 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + 1) := by
  rw [pow_four_sub_one_eq_sq_sub_one_mul_sq_add_one hq]
  ring

/-- The elementary case split behind “otherwise `ell` divides `q^2+1`”. -/
theorem prime_dvd_q_sq_add_one_of_dvd_sp4_factored_order
    {q ell : ℕ} (hell : ell.Prime)
    (horder : ell ∣ q ^ 4 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + 1))
    (hellq : ¬ell ∣ q) (hellqm : ¬ell ∣ q ^ 2 - 1) :
    ell ∣ q ^ 2 + 1 := by
  rcases hell.dvd_mul.mp horder with hleft | hright
  · rcases hell.dvd_mul.mp hleft with hq | hqm
    · exact (hellq (hell.dvd_of_dvd_pow hq)).elim
    · exact (hellqm (hell.dvd_of_dvd_pow hqm)).elim
  · exact hright

/-- Under the two nondivisibility hypotheses, the full `ell`-part of the
factored order divides `q^2+1`. -/
theorem sp4_factored_order_full_part_dvd_q_sq_add_one
    {q ell : ℕ} (hell : ell.Prime) (hq : q ≠ 0)
    (hqm : q ^ 2 - 1 ≠ 0) (hellq : ¬ell ∣ q)
    (hellqm : ¬ell ∣ q ^ 2 - 1) :
    ordProj[ell] (q ^ 4 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + 1)) ∣
      q ^ 2 + 1 := by
  apply ordProj_mul_dvd_right_of_not_dvd_left
  · exact mul_ne_zero (pow_ne_zero 4 hq) (pow_ne_zero 2 hqm)
  · omega
  · intro h
    rcases hell.dvd_mul.mp h with h | h
    · exact hellq (hell.dvd_of_dvd_pow h)
    · exact hellqm (hell.dvd_of_dvd_pow h)

/-- Manuscript-shaped composition of the checked arithmetic and finite group
steps.  The concrete order formula, cyclic torus, and nondivisibility facts
are explicit inputs. -/
theorem order_and_cyclic_torus_force_cyclic_ell_subgroups
    {G : Type*} [Group G] [Finite G] {q ell : ℕ}
    (hell : ell.Prime) (hq : 2 < q) (hellq : ¬ell ∣ q)
    (hellqm : ¬ell ∣ q ^ 2 - 1)
    (hcardG : Nat.card G = q ^ 4 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + 1))
    (T : Subgroup G) [IsCyclic T] (hcardT : Nat.card T = q ^ 2 + 1)
    (D : Subgroup G) (hD : IsPGroup ell D) : IsCyclic D := by
  let _ : Fact ell.Prime := ⟨hell⟩
  have hq0 : q ≠ 0 := by omega
  have hqm0 : q ^ 2 - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (one_lt_pow₀ (by omega) (by decide))
  apply isCyclic_of_isPGroup_of_full_part_dvd_card_cyclic_subgroup T _ D hD
  simpa only [hcardG, hcardT] using
    sp4_factored_order_full_part_dvd_q_sq_add_one
      hell hq0 hqm0 hellq hellqm

end ModularRep.ManuscriptVerification.RankTwoSymplectic


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
