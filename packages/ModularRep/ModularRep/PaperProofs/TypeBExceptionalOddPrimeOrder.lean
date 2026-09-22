import ModularRep.PaperProofs.TypeBSpinCoverSource
import ModularRep.CyclicSylow
import Mathlib.Tactic.NormNum

/-!
# The elementary exceptional odd-prime deduction on the exact cover

FLZ, proof of Theorem 1, p. 574, gives the order of the full cover
6.Omega_7(3). Malle--Testerman, Tables 24.2--24.3 and Remark 24.19,
pp. 211--214, identify the exceptional multiplier C6. The carrier below
is matched to the actual Spin/centre quotient and retains its full
universal ell-prime-cover certificate. It is not Spin or 3.Omega.

The only conclusion is cyclicity of every ell-subgroup at 5, 7 and 13.
The source identification of H and its order is E1/U. No cyclic-defect
block theorem, character-triple witness, or final condition is an input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBExceptionalOddPrimeOrder

open ModularRep TypeBCliffordCarriers TypeBSpinCoverSource
open EvenFieldFLZSourceConditions

inductive ExceptionalPrime where
  | five | seven | thirteen
  deriving DecidableEq

def ExceptionalPrime.value : ExceptionalPrime → ℕ
  | .five => 5
  | .seven => 7
  | .thirteen => 13

theorem ExceptionalPrime.prime (t : ExceptionalPrime) : Nat.Prime t.value := by
  cases t <;> decide

def fullCoverOrder : ℕ := 2 ^ 10 * 3 ^ 10 * 5 * 7 * 13

/-- The order admits no further odd nondefining prime branch. -/
theorem exists_exceptionalPrime {ell : ℕ} (hEll : ell.Prime)
    (hOdd : Odd ell) (hNondef : ell ≠ 3) (hdiv : ell ∣ fullCoverOrder) :
    ∃ t : ExceptionalPrime, ell = t.value := by
  rw [fullCoverOrder] at hdiv
  rcases hEll.dvd_mul.mp hdiv with h2357 | h13
  · rcases hEll.dvd_mul.mp h2357 with h235 | h7
    · rcases hEll.dvd_mul.mp h235 with h23 | h5
      · rcases hEll.dvd_mul.mp h23 with h2 | h3
        · have heq := (Nat.prime_dvd_prime_iff_eq hEll Nat.prime_two).mp
            (hEll.dvd_of_dvd_pow h2)
          subst ell
          norm_num at hOdd
        · exact (hNondef ((Nat.prime_dvd_prime_iff_eq hEll (by decide)).mp
            (hEll.dvd_of_dvd_pow h3))).elim
      · exact ⟨.five, (Nat.prime_dvd_prime_iff_eq hEll (by decide)).mp h5⟩
    · exact ⟨.seven, (Nat.prime_dvd_prime_iff_eq hEll (by decide)).mp h7⟩
  · exact ⟨.thirteen, (Nat.prime_dvd_prime_iff_eq hEll (by decide)).mp h13⟩

theorem fullPrimePart (t : ExceptionalPrime) :
    t.value ^ fullCoverOrder.factorization t.value = t.value := by
  have hn : fullCoverOrder ≠ 0 := by norm_num [fullCoverOrder]
  have hlower : 1 ≤ fullCoverOrder.factorization t.value :=
    (t.prime.dvd_iff_one_le_factorization hn).mp (by
      cases t <;> norm_num [ExceptionalPrime.value, fullCoverOrder])
  have hupper : fullCoverOrder.factorization t.value < 2 := by
    rw [← not_le]
    intro h
    have hdvd := (t.prime.pow_dvd_iff_le_factorization hn).mpr h
    cases t <;> norm_num [ExceptionalPrime.value, fullCoverOrder] at hdvd
  have heq : fullCoverOrder.factorization t.value = 1 := by omega
  simp [heq]

/-- Pure order calculation, kept separate from the exact source carrier. -/
theorem everyPrimeSubgroupCyclic_of_order
    (t : ExceptionalPrime) {H : Type} [Group H] [Finite H]
    (hcard : Nat.card H = fullCoverOrder) (D : Subgroup H)
    (hD : IsPGroup t.value D) : IsCyclic D := by
  let _ : Fact (Nat.Prime t.value) := ⟨t.prime⟩
  let P : Sylow t.value H := default
  have hP : Nat.card P = t.value := by
    rw [P.card_eq_multiplicity, hcard, fullPrimePart]
  let _ : IsCyclic P := isCyclic_of_prime_card hP
  apply CyclicSylow.isCyclic_of_isPGroup_of_full_part_dvd_card_cyclic_subgroup
    P _ D hD
  rw [hP, hcard, fullPrimePart]

/-- The manuscript exceptional deduction on the SAME universal ell-prime
cover of the actual Omega_7(3) quotient. The quotient match and cover
certificate remain explicit E1/U arguments even though the last arithmetic
step only needs their group's order. No unproved full block condition is
selected by these source data. -/
theorem exceptionalCover_everyPrimeSubgroupCyclic
    (N : NormSource 3 (ZMod 3)) (t : ExceptionalPrime)
    {H : Type} [Group H] [Fintype H]
    (cover : EllPrimeCoverSource t.value H)
    (simpleQuotient : cover.S ≃* Omega N)
    (hcard : Nat.card H = fullCoverOrder) :
    ∀ D : Subgroup H, IsPGroup t.value D → IsCyclic D :=
  everyPrimeSubgroupCyclic_of_order t hcard

/-- Exhaustive exceptional deduction for every odd nondefining prime
dividing the ACTUAL simple quotient. Surjectivity of the same covering map
first carries its divisibility to the covering order; Lean selects one of
5, 7 and 13 and proves cyclicity on this cover's own subgroups. -/
theorem exceptionalCover_everyOddNondefiningSubgroupCyclic
    (N : NormSource 3 (ZMod 3)) {ell : ℕ}
    (hEll : ell.Prime) (hOdd : Odd ell) (hNondef : ell ≠ 3)
    {H : Type} [Group H] [Fintype H]
    (cover : EllPrimeCoverSource ell H)
    (simpleQuotient : cover.S ≃* Omega N)
    (hdiv : ell ∣ Nat.card (Omega N))
    (hcard : Nat.card H = fullCoverOrder) :
    ∀ D : Subgroup H, IsPGroup ell D → IsCyclic D := by
  have hSource : ell ∣ Nat.card cover.S := by
    rwa [Nat.card_congr simpleQuotient.toEquiv]
  have hCover : ell ∣ Nat.card H := hSource.trans
    (Subgroup.card_dvd_of_surjective cover.quotient cover.quotient_surjective)
  obtain ⟨t, ht⟩ := exists_exceptionalPrime hEll hOdd hNondef (hcard ▸ hCover)
  intro D hD
  exact everyPrimeSubgroupCyclic_of_order t hcard D (ht ▸ hD)

end ModularRep.PaperProofs.TypeBExceptionalOddPrimeOrder


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
