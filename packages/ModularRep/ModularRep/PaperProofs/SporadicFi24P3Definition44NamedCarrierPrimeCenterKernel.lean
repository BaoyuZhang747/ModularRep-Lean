import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralSector
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! The actual central kernel is either trivial or the full centre when
the centre has prime order. This gives an exhaustive packet split without
an ordinary central character classification premise. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterKernel

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

universe u

theorem centralKernel_eq_bot_or_center
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (hprime : (Nat.card (Subgroup.center P.H)).Prime) :
    centralCharacterKernel P psi = ⊥ ∨
      centralCharacterKernel P psi = Subgroup.center P.H := by
  let Z := Subgroup.center P.H
  let Z0 := centralCharacterKernel P psi
  let : Fact (Nat.card Z).Prime := ⟨hprime⟩
  rcases (Z0.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with h | h
  · left
    have hm := congrArg (Subgroup.map Z.subtype) h
    simpa only [Subgroup.map_subgroupOf_eq_of_le
      (show Z0 ≤ Z from inf_le_left), Subgroup.map_bot] using hm
  · right
    exact le_antisymm inf_le_left (Subgroup.subgroupOf_eq_top.mp h)

theorem brauerCenterTrivial_of_kernel_eq_center
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (hZ0 : centralCharacterKernel P psi = Subgroup.center P.H) :
    ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
      psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩ := by
  intro z
  have hz : (z.1 : P.H) ∈ centralCharacterKernel P psi := by
    rw [hZ0]
    exact z.1.2
  rw [chosenBrauerRepresentation_character]
  exact brauer_apply_eq_one_of_mem_ker
    (chosenBrauerRepresentation P psi).ρ P.iota
    (PrimeRegularElement.map (Subgroup.center P.H).subtype z) hz.2

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
