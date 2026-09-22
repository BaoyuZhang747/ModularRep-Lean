import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralStabilizer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

/-! The ordinary faithful central-sector condition implies faithfulness
of the actual chosen modular representation on the full centre. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralSector

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

private theorem root_lift_one {p : ℕ} {k K G : Type*}
    [Field k] [Field K] [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) : iota.lift (1 : k) = (1 : K) := by
  simpa [PrimeRegularRootEmbedding.liftRoot] using
    iota.lift_coe (1 : rootsOfUnity (primeRegularExponent p G) k)

theorem brauer_degree_ne_zero
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P) :
    psi.1.1 ⟨1, isPrimeRegular_one⟩ ≠ 0 := by
  let V := chosenBrauerRepresentation P psi
  let : Representation.IsIrreducible V.ρ := chosenBrauerRepresentation_irreducible P psi
  let : Nontrivial (Representation.asModule V.ρ) :=
    IsSimpleModule.nontrivial P.k[P.H] (Representation.asModule V.ρ)
  let : Nontrivial V := (Representation.asModuleEquiv V.ρ).symm.toEquiv.nontrivial
  have hpos : 0 < Module.finrank P.k V := Module.finrank_pos
  have hvalue : psi.1.1 ⟨1, isPrimeRegular_one⟩ = (Module.finrank P.k V : P.K) := by
    rw [chosenBrauerRepresentation_character]
    simpa [root_lift_one] using Representation.brauerCharacterOfRootEmbedding_apply_central
      V.ρ P.iota (Subgroup.center P.H) le_rfl 1 isPrimeRegular_one
  rw [hvalue]
  exact Nat.cast_ne_zero.mpr hpos.ne'

theorem centralCharacterKernel_eq_bot_of_faithful_liesOver
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (lambda : OrdinaryIrreducibleCharacter.Irr P.K (Subgroup.center P.H))
    (hLambda : ∀ z, lambda z = lambda 1 → z = 1)
    (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
      psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩ * lambda z.1) :
    centralCharacterKernel P psi = ⊥ := by
  apply bot_unique
  intro x hx
  let z : Subgroup.center P.H := ⟨x, hx.1⟩
  have hz : IsPrimeRegular P.p z :=
    IsPrimeRegular.of_coprime_natCard
      (P.iota.prime.coprime_iff_not_dvd.mpr hcenter).symm z
  have hzval : psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype ⟨z, hz⟩) =
      psi.1.1 ⟨1, isPrimeRegular_one⟩ := by
    rw [chosenBrauerRepresentation_character]
    exact brauer_apply_eq_one_of_mem_ker (chosenBrauerRepresentation P psi).ρ P.iota
      (PrimeRegularElement.map (Subgroup.center P.H).subtype ⟨z, hz⟩) hx.2
  have h1 := hglobal ⟨1, isPrimeRegular_one⟩
  change psi.1.1 ⟨1, isPrimeRegular_one⟩ =
    psi.1.1 ⟨1, isPrimeRegular_one⟩ * lambda 1 at h1
  have hlambda : lambda z = lambda 1 :=
    mul_left_cancel₀ (brauer_degree_ne_zero P psi)
      ((hglobal ⟨z, hz⟩).symm.trans (hzval.trans h1))
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hLambda z hlambda))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralSector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
