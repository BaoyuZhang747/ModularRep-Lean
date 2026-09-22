import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Int.ModEq

/-!
# Arithmetic of two powers on one component orbit

The two orbit lengths are computed from the same component permutation.
Only the original component-return equation is an input. The nonpositive
representative, both divisibilities, and natural power exponents are derived.
No assertion about a character, a rational fixed-point action, or a standard
realisation of a geometric component is an input or conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnPowerArithmetic

variable {I : Type*}

/-- The actual period of one component under the specified permutation. -/
abbrev orbitLength (sigma : Equiv.Perm I) (j : I) : ℕ :=
  MulAction.period sigma j

/-- Finite component permutations have positive actual orbit lengths. -/
theorem orbitLength_pos [Finite I] (sigma : Equiv.Perm I) (j : I) :
    0 < orbitLength sigma j := by
  change 0 < Function.minimalPeriod sigma j
  exact Function.minimalPeriod_pos_of_mem_periodicPts (sigma.injective.mem_periodicPts j)

/-- A nonpositive representative is chosen by reducing the negative exponent. -/
def nonpositiveRepresentative (k : ℤ) (d : ℕ) : ℤ := -((-k) % (d : ℤ))

theorem nonpositiveRepresentative_nonpos (k : ℤ) {d : ℕ} (hd : 0 < d) :
    nonpositiveRepresentative k d ≤ 0 := by
  exact neg_nonpos.mpr (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (ne_of_gt hd)))

theorem nonpositiveRepresentative_modEq (k : ℤ) (d : ℕ) :
    Int.ModEq (d : ℤ) (nonpositiveRepresentative k d) k := by
  simpa only [nonpositiveRepresentative, neg_neg] using
    (Int.neg_modEq_neg.mpr (Int.mod_modEq (-k) (d : ℤ)))

/-- Congruence modulo the actual orbit length preserves the component image. -/
theorem zpow_apply_eq_of_modEq (sigma : Equiv.Perm I) (j : I) {m n : ℤ}
    (hmn : Int.ModEq (orbitLength sigma j : ℤ) m n) :
    (sigma ^ m) j = (sigma ^ n) j := by
  calc
    (sigma ^ m) j = (sigma ^ (m % (orbitLength sigma j : ℤ))) j :=
      (MulAction.zpow_mod_period_smul (g := sigma) (a := j) m).symm
    _ = (sigma ^ (n % (orbitLength sigma j : ℤ))) j :=
      congrArg (fun z : ℤ => (sigma ^ z) j) hmn.eq
    _ = (sigma ^ n) j :=
      MulAction.zpow_mod_period_smul (g := sigma) (a := j) n

/-- The period of F₀ divides h times the period of F₀ to the h-th power. -/
theorem orbitLength_dvd_power_orbitLength (sigma : Equiv.Perm I) (j : I) (h : ℕ) :
    orbitLength sigma j ∣ h * orbitLength (sigma ^ h) j := by
  apply (MulAction.pow_smul_eq_iff_period_dvd (m := sigma) (a := j)).mp
  change (sigma ^ (h * orbitLength (sigma ^ h) j)) j = j
  have hfixed : ((sigma ^ h) ^ orbitLength (sigma ^ h) j) j = j :=
    MulAction.pow_period_smul (sigma ^ h) j
  simpa only [pow_mul] using hfixed

/-- Equality of the two original component images forces the return exponent
 to be divisible by the actual F₀ orbit length. -/
theorem orbitLength_dvd_return (sigma : Equiv.Perm I) (j : I)
    (a t h : ℕ) (k : ℤ)
    (hreturn : (sigma ^ (a * t)) j = ((sigma ^ h) ^ k) j) :
    (orbitLength sigma j : ℤ) ∣ (a : ℤ) * t - (h : ℤ) * k := by
  have heq : (sigma ^ ((a : ℤ) * t)) j = (sigma ^ ((h : ℤ) * k)) j := by
    simpa only [← Nat.cast_mul, zpow_mul, zpow_natCast] using hreturn
  apply (MulAction.zpow_smul_eq_iff_period_dvd (g := sigma) (a := j)).mp
  change (sigma ^ ((a : ℤ) * t - (h : ℤ) * k)) j = j
  apply (sigma ^ ((h : ℤ) * k)).injective
  rw [← Equiv.Perm.mul_apply, ← zpow_add]
  have hsum : (h : ℤ) * k + ((a : ℤ) * t - (h : ℤ) * k) = (a : ℤ) * t := by
    omega
  rw [hsum]
  exact heq

/-- Nonnegative divisible exponents give natural powers of the common return. -/
theorem exists_nat_multipliers {u n : ℕ} {v : ℤ}
    (hv : 0 ≤ v) (hu : (u : ℤ) ∣ v) (hn : u ∣ n) :
    ∃ r s : ℕ, v = (u : ℤ) * r ∧ n = u * s := by
  have hnat : u ∣ v.toNat := by
    apply Int.natCast_dvd_natCast.mp
    rw [Int.toNat_of_nonneg hv]
    exact hu
  obtain ⟨r, hr⟩ := hnat
  obtain ⟨s, hs⟩ := hn
  refine ⟨r, s, ?_, hs⟩
  have heq := congrArg (fun z : ℕ => (z : ℤ)) hr
  simpa only [Nat.cast_mul, Int.toNat_of_nonneg hv] using heq

/-- Choose k in its original congruence class modulo the actual F orbit length.
 Both exponents are then powers of the same actual F₀ component return. -/
theorem exists_nonpositive_return [Finite I] (sigma : Equiv.Perm I) (j : I)
    (a t h : ℕ) (k0 : ℤ)
    (hreturn : (sigma ^ (a * t)) j = ((sigma ^ h) ^ k0) j) :
    ∃ k : ℤ, k ≤ 0 ∧
      Int.ModEq (orbitLength (sigma ^ h) j : ℤ) k k0 ∧
      (sigma ^ (a * t)) j = ((sigma ^ h) ^ k) j ∧
      0 ≤ (a : ℤ) * t - (h : ℤ) * k ∧
      (orbitLength sigma j : ℤ) ∣ (a : ℤ) * t - (h : ℤ) * k ∧
      orbitLength sigma j ∣ h * orbitLength (sigma ^ h) j ∧
      ∃ r s : ℕ,
        (a : ℤ) * t - (h : ℤ) * k = (orbitLength sigma j : ℤ) * r ∧
        h * orbitLength (sigma ^ h) j = orbitLength sigma j * s := by
  let k := nonpositiveRepresentative k0 (orbitLength (sigma ^ h) j)
  have hk : k ≤ 0 := nonpositiveRepresentative_nonpos k0 (orbitLength_pos _ _)
  have hmod : Int.ModEq (orbitLength (sigma ^ h) j : ℤ) k k0 :=
    nonpositiveRepresentative_modEq k0 _
  have hsame : (sigma ^ (a * t)) j = ((sigma ^ h) ^ k) j :=
    hreturn.trans (zpow_apply_eq_of_modEq (sigma ^ h) j hmod).symm
  have hnonneg : 0 ≤ (a : ℤ) * t - (h : ℤ) * k := by
    have hleft : 0 ≤ (a : ℤ) * t := mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg t)
    have hright : (h : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg h) hk
    omega
  have hdiv := orbitLength_dvd_return sigma j a t h k hsame
  have hperiod := orbitLength_dvd_power_orbitLength sigma j h
  exact ⟨k, hk, hmod, hsame, hnonneg, hdiv, hperiod,
    exists_nat_multipliers hnonneg hdiv hperiod⟩

/-- The input may be just membership in the original F-component orbit.
 It does not prescribe a return action on a character or a fixed-point group. -/
theorem exists_nonpositive_return_of_sameCycle [Finite I]
    (sigma : Equiv.Perm I) (j : I) (a t h : ℕ)
    (hcycle : (sigma ^ h).SameCycle j ((sigma ^ (a * t)) j)) :
    ∃ k : ℤ, k ≤ 0 ∧
      (sigma ^ (a * t)) j = ((sigma ^ h) ^ k) j ∧
      ∃ r s : ℕ,
        (a : ℤ) * t - (h : ℤ) * k = (orbitLength sigma j : ℤ) * r ∧
        h * orbitLength (sigma ^ h) j = orbitLength sigma j * s := by
  obtain ⟨k0, hk0⟩ := hcycle
  obtain ⟨k, hk, _, hsame, _, _, _, hpowers⟩ :=
    exists_nonpositive_return sigma j a t h k0 hk0.symm
  exact ⟨k, hk, hsame, hpowers⟩

/-- The corrected return is a natural endomorphism power because k is nonpositive. -/
theorem natural_return_exponent {a t h u r : ℕ} {k : ℤ}
    (hk : k ≤ 0) (heq : (a : ℤ) * t - (h : ℤ) * k = (u : ℤ) * r) :
    a * t + h * (-k).toNat = u * r := by
  apply Int.natCast_inj.mp
  simp only [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg (neg_nonneg.mpr hk)]
  rw [mul_neg, ← sub_eq_add_neg]
  exact heq

/-- Natural powers for an endomorphism-only fixed-point transport. -/
theorem exists_natural_return_powers [Finite I]
    (sigma : Equiv.Perm I) (j : I) (a t h : ℕ)
    (hcycle : (sigma ^ h).SameCycle j ((sigma ^ (a * t)) j)) :
    ∃ k : ℤ, k ≤ 0 ∧
      (sigma ^ (a * t)) j = ((sigma ^ h) ^ k) j ∧
      ∃ r s : ℕ,
        a * t + h * (-k).toNat = orbitLength sigma j * r ∧
        h * orbitLength (sigma ^ h) j = orbitLength sigma j * s := by
  obtain ⟨k, hk, hsame, r, s, hr, hs⟩ :=
    exists_nonpositive_return_of_sameCycle sigma j a t h hcycle
  exact ⟨k, hk, hsame, r, s, natural_return_exponent hk hr, hs⟩

end ModularRep.PaperProofs.TypeBLeviReturnPowerArithmetic


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
