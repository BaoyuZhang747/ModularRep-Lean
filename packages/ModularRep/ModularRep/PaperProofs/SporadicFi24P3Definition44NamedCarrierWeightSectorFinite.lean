import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import Mathlib.SetTheory.Cardinal.Finite

/-! # The actual sector counts imply finiteness of all original weights -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierWeightSectorFinite

open SporadicFi24CentralSectorAssemblyLemma56Actual

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

omit [CharP k 2] in
theorem weight_finite_of_sector_counts
    (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
    (hWt41 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = 1} = 41)
    (hWt25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // weightSector (R := R) w = nu} = 25) :
    Finite (WeightClass (p := 2) (K := K) (X := X)) := by
  classical
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  have hsector (nu : CentralSector (k := k) (X := X)) :
      Finite {w : WeightClass (p := 2) (K := K) (X := X) // weightSector (R := R) w = nu} := by
    apply Nat.finite_of_card_ne_zero
    by_cases hnu : nu = 1
    · subst nu
      rw [hWt41]
      decide
    · rw [hWt25 nu hnu]
      decide
  let _ : ∀ b : ActualBlock (k := k) (X := X),
      Finite {w : WeightClass (p := 2) (K := K) (X := X) //
        weightSector (R := R) w = blockSector b} := fun b => hsector (blockSector b)
  let S := Σ b : ActualBlock (k := k) (X := X),
    {w : WeightClass (p := 2) (K := K) (X := X) // weightSector (R := R) w = blockSector b}
  exact Finite.of_surjective (fun s : S => s.2.1)
    (fun w => ⟨⟨R.1.weightBlock w, ⟨w, rfl⟩⟩, rfl⟩)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierWeightSectorFinite


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
