import ModularRep.PaperProofs.TypeBSpinStabilizer
import Mathlib.GroupTheory.Index

/-!
# The literal index in FLZ Remark 2.2

The source diagonal homomorphism has kernel Spin times the centre. The
first isomorphism theorem therefore computes the order of this precise
quotient, rather than that of special Clifford modulo Spin alone.
The E1 locator for the homomorphism/kernel is FLZ proof of Theorem 3.7,
p. 545; Remark 2.2, p. 537 consumes its prime-to-ell consequence.
Character-theoretic J_G semantics remain a separate source obligation.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCliffordIndexCompatibility

open TypeBCliffordCarriers TypeBSpinStabilizer

variable {n : ℕ} {F : Type} [Field F] (N : NormSource n F)

/-- The quotient in Remark 2.2 is the actual quotient by Spin and centre. -/
theorem specialClifford_quotient_order_two
    (diagonal : SpecialClifford n F →* DiagonalGroup)
    (surjective : Function.Surjective diagonal)
    (kernel : diagonal.ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)) :
    Nat.card (SpecialClifford n F ⧸
      (SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))) = 2 := by
  have hc := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective diagonal surjective).toEquiv
  simpa only [kernel, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card] using hc

/-- The numerical hypothesis used by the published automatic-compatibility
clause is derived for the literal quotient at every odd modular prime. -/
theorem oddPrime_not_dvd_specialClifford_quotient
    {ell : ℕ} (hEll : Nat.Prime ell) (hOdd : Odd ell)
    (diagonal : SpecialClifford n F →* DiagonalGroup)
    (surjective : Function.Surjective diagonal)
    (kernel : diagonal.ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)) :
    ¬ ell ∣ Nat.card (SpecialClifford n F ⧸
      (SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))) := by
  rw [specialClifford_quotient_order_two N diagonal surjective kernel]
  intro hd
  have he : ell = 2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hEll.ne_one
  have : ¬ Odd (2 : ℕ) := by decide
  exact this (he ▸ hOdd)

/-- The subgroup computation behind the automatic `J_G` clause. Here `hall`
is the preimage of the Hall ell-prime subgroup of the cyclic quotient by
Spin, so its index is an ell-power. Each inertia contains Spin and centre.
These source-sized hypotheses imply that its join with `hall` is all of
special Clifford. Identification with character/weight `J_G` definitions
is separate; no character correspondence or compatibility is assumed. -/
theorem inertia_sup_hall_eq_top
    {ell a : ℕ} (hOdd : Odd ell)
    (diagonal : SpecialClifford n F →* DiagonalGroup)
    (surjective : Function.Surjective diagonal)
    (kernel : diagonal.ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))
    (inertia hall : Subgroup (SpecialClifford n F))
    (contains : SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) ≤ inertia)
    (hallIndex : hall.index = ell ^ a) : inertia ⊔ hall = ⊤ := by
  apply Subgroup.index_eq_one.mp
  have htwo : (SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)).index = 2 :=
    specialClifford_quotient_order_two N diagonal surjective kernel
  have hdTwo : (inertia ⊔ hall).index ∣ 2 := by
    rw [← htwo]
    exact Subgroup.index_dvd_of_le (contains.trans le_sup_left)
  have hdHall : (inertia ⊔ hall).index ∣ ell ^ a := by
    rw [← hallIndex]
    exact Subgroup.index_dvd_of_le le_sup_right
  exact Nat.eq_one_of_dvd_coprimes (hOdd.coprime_two_left.pow_right a) hdTwo hdHall

end ModularRep.PaperProofs.TypeBCliffordIndexCompatibility


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
