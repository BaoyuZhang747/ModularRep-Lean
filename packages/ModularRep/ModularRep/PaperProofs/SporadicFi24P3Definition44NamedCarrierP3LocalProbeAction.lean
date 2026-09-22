import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! The local four-character action from one separating value probe.
The two quotient elements, their eight character values and the conjugacy
image of the first element are explicit carrier/action bindings. No fixed
count, row action or complete class representative list is supplied. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalProbeAction

open ModularRep ModularRep.CharacterWeight
open CyclicOuterLemma37Concrete

universe u

def rowPermutation : Equiv.Perm (Fin 4) := Equiv.swap 2 3

theorem probe_values_injective {K : Type u} [Field K] [CharZero K]
    (z : K) (hz : z * z = -1) :
    Function.Injective (![-1, 1, z, -z] : Fin 4 → K) := by
  have hn : z ≠ -z := by
    intro h
    have ht : (2 : K) * z = 0 := by linear_combination h
    have hzero : z = 0 := (mul_eq_zero.mp ht).resolve_left (by norm_num)
    rw [hzero] at hz
    norm_num at hz
  have hp : z ≠ 1 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hm : z ≠ -1 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hnp : -z ≠ 1 := by
    intro h
    apply hm
    linear_combination -h
  have hnm : -z ≠ -1 := by simpa using hp
  have hps := Ne.symm hp
  have hms := Ne.symm hm
  have hns := Ne.symm hn
  have hnps := Ne.symm hnp
  intro r s h
  fin_cases r <;> fin_cases s <;> (try norm_num at h) <;> first | rfl | contradiction

theorem probe_values_transition {K : Type u} [Field K] (z : K) (r : Fin 4) :
    (![-1, 1, -z, z] : Fin 4 → K) r =
      (![-1, 1, z, -z] : Fin 4 → K) (rowPermutation r) := by
  fin_cases r <;> simp [rowPermutation, Equiv.swap_apply_def]

theorem rowPermutation_fixed_card :
    Nat.card {r : Fin 4 // rowPermutation r = r} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

variable {p : ℕ} {K G : Type u} [Field K] [CharZero K] [Group G] [Fintype G]
variable (Q : RadicalSubgroup (p := p) (G := G))
variable (rows : Fin 4 → LocalDefectZeroCharacter (K := K) Q)
variable (complete : Function.Surjective rows)
variable (beta : MulAut (NormalizerQuotient Q.1))
variable (x y : NormalizerQuotient Q.1) (z : K) (hz : z * z = -1)
variable (values : ∀ r, (rows r).1 x = (![-1, 1, z, -z] : Fin 4 → K) r)
variable (imageValues : ∀ r, (rows r).1 y = (![-1, 1, -z, z] : Fin 4 → K) r)
variable (fusion : ∃ a : NormalizerQuotient Q.1, beta x = a * y * a⁻¹)

include hz values in
theorem local_rows_injective : Function.Injective rows := by
  intro r s h
  apply probe_values_injective z hz
  exact (values r).symm.trans
    ((congrArg (fun theta : LocalDefectZeroCharacter (K := K) Q => theta.1 x) h).trans
      (values s))

include complete hz values imageValues fusion in
theorem local_rows_twist (r : Fin 4) :
    OrdinaryIrreducibleCharacter.twist K _ (rows r).1 beta =
      (rows (rowPermutation r)).1 := by
  let moved : LocalDefectZeroCharacter (K := K) Q :=
    ⟨OrdinaryIrreducibleCharacter.mapEquiv (rows r).1 beta.symm,
      (rows r).2.mapEquiv beta.symm⟩
  obtain ⟨s, hs⟩ := complete moved
  have hv (w : NormalizerQuotient Q.1) :
      (rows s).1 w = (rows r).1 (beta w) :=
    congrArg (fun theta : LocalDefectZeroCharacter (K := K) Q => theta.1 w) hs
  have hi : s = rowPermutation r := by
    apply probe_values_injective z hz
    obtain ⟨a, ha⟩ := fusion
    calc
      (![-1, 1, z, -z] : Fin 4 → K) s = (rows s).1 x := (values s).symm
      _ = (rows r).1 (beta x) := hv x
      _ = (rows r).1 y := by
        rw [ha]
        exact ordinaryCharacter_conj (rows r).1 a y
      _ = (![-1, 1, -z, z] : Fin 4 → K) r := imageValues r
      _ = (![-1, 1, z, -z] : Fin 4 → K) (rowPermutation r) :=
        probe_values_transition z r
  apply OrdinaryIrreducibleCharacter.ext
  intro w
  exact (hv w).symm.trans (congrArg (fun j : Fin 4 => (rows j).1 w) hi)

include complete hz values imageValues fusion in
theorem local_fixed_card_two :
    Nat.card {theta : LocalDefectZeroCharacter (K := K) Q //
      OrdinaryIrreducibleCharacter.twist K _ theta.1 beta = theta.1} = 2 := by
  have hinj := local_rows_injective Q rows x z hz values
  let e := Equiv.ofBijective rows ⟨hinj, complete⟩
  have hf (r : Fin 4) : rowPermutation r = r ↔
      OrdinaryIrreducibleCharacter.twist K _ (rows r).1 beta = (rows r).1 := by
    rw [local_rows_twist Q rows complete beta x y z hz values imageValues fusion r]
    constructor
    · intro h
      rw [h]
    · intro h
      exact hinj (Subtype.ext h)
  let ef : {r : Fin 4 // rowPermutation r = r} ≃
      {theta : LocalDefectZeroCharacter (K := K) Q //
        OrdinaryIrreducibleCharacter.twist K _ theta.1 beta = theta.1} :=
    e.subtypeEquiv hf
  exact (Nat.card_congr ef).symm.trans rowPermutation_fixed_card

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalProbeAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
