import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralSector

/-! The literal trivial central-sector equation identifies the kernel used by
the own central quotient with the full centre. Root-lift injectivity is used
only on a root obtained from the chosen representation's characteristic polynomial. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCentralSector

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralSector

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H := Fintype.ofFinite H

private theorem eq_one_of_lift_eq_one_on_charpoly_root
    {p : ℕ} {k K G V : Type*}
    [Field k] [Field K] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V)
    (iota : PrimeRegularRootEmbedding p k K G)
    (g : PrimeRegularElement (G := G) p)
    (a : {a : k // a ∈ (rho g.1).charpoly.roots})
    (h : iota.lift a.1 = 1) :
    a.1 = 1 := by
  have hinj : Function.Injective iota.liftRoot :=
    Units.val_injective.comp
      (Subtype.val_injective.comp iota.toMulEquiv.injective)
  have hroot : rho.charpolyRootAsRootOfUnity iota g a = 1 := by
    apply hinj
    calc
      iota.liftRoot (rho.charpolyRootAsRootOfUnity iota g a) =
          iota.lift a.1 :=
        (rho.lift_charpolyRootAsRootOfUnity iota g a).symm
      _ = 1 := h
      _ = iota.liftRoot 1 := by
        simp [PrimeRegularRootEmbedding.liftRoot]
  simpa using congrArg
    (fun t : rootsOfUnity (primeRegularExponent p G) k =>
      ((t : kˣ) : k)) hroot

theorem centralCharacterKernel_eq_center_of_trivial_sector
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (hglobal : ∀ z : PrimeRegularElement
        (G := Subgroup.center P.H) P.p,
      psi.1.1
          (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩) :
    centralCharacterKernel P psi = Subgroup.center P.H := by
  let V := chosenBrauerRepresentation P psi
  let : Representation.IsIrreducible V.ρ :=
    chosenBrauerRepresentation_irreducible P psi
  have hlift_one : P.iota.lift (1 : P.k) = (1 : P.K) := by
    simpa [PrimeRegularRootEmbedding.liftRoot] using
      P.iota.lift_coe
        (1 : rootsOfUnity (primeRegularExponent P.p P.H) P.k)
  have hdegree :
      psi.1.1 ⟨1, isPrimeRegular_one⟩ =
        (Module.finrank P.k V : P.K) := by
    rw [chosenBrauerRepresentation_character]
    simpa [hlift_one] using
      Representation.brauerCharacterOfRootEmbedding_apply_central
        V.ρ P.iota (Subgroup.center P.H) le_rfl 1 isPrimeRegular_one
  have hdim : (Module.finrank P.k V : P.K) ≠ 0 := by
    rw [← hdegree]
    exact brauer_degree_ne_zero P psi
  have hn : Module.finrank P.k V ≠ 0 :=
    Nat.cast_ne_zero.mp hdim
  apply le_antisymm
    (show centralCharacterKernel P psi ≤ Subgroup.center P.H
      from inf_le_left)
  intro x hx
  refine ⟨hx, ?_⟩
  let z : Subgroup.center P.H := ⟨x, hx⟩
  have hzZ : IsPrimeRegular P.p z :=
    IsPrimeRegular.of_coprime_natCard
      (P.iota.prime.coprime_iff_not_dvd.mpr hcenter).symm z
  have hzG : IsPrimeRegular P.p x :=
    hzZ.map (Subgroup.center P.H).subtype
  let a : P.k :=
    (Representation.centralCharacter V.ρ (Subgroup.center P.H) le_rfl z : P.k)
  have hroot : a ∈ (V.ρ x).charpoly.roots := by
    change a ∈ (V.ρ (z : P.H)).charpoly.roots
    rw [Representation.centralCharacter_spec V.ρ (Subgroup.center P.H) le_rfl z,
      Representation.roots_charpoly_smul_id]
    exact Multiset.mem_replicate.mpr ⟨hn, rfl⟩
  have hvalue :
      psi.1.1
          (PrimeRegularElement.map (Subgroup.center P.H).subtype
            ⟨z, hzZ⟩) =
        (Module.finrank P.k V : P.K) * P.iota.lift a := by
    rw [chosenBrauerRepresentation_character]
    exact Representation.brauerCharacterOfRootEmbedding_apply_central V.ρ
      P.iota (Subgroup.center P.H) le_rfl z hzG
  have hlift : P.iota.lift a = 1 := by
    apply mul_left_cancel₀ hdim
    calc
      (Module.finrank P.k V : P.K) * P.iota.lift a =
          psi.1.1
            (PrimeRegularElement.map (Subgroup.center P.H).subtype
              ⟨z, hzZ⟩) := hvalue.symm
      _ = psi.1.1 ⟨1, isPrimeRegular_one⟩ := hglobal ⟨z, hzZ⟩
      _ = (Module.finrank P.k V : P.K) * 1 := by
        simpa using hdegree
  have ha : a = 1 :=
    eq_one_of_lift_eq_one_on_charpoly_root
      V.ρ P.iota ⟨x, hzG⟩ ⟨a, hroot⟩ hlift
  change V.ρ x = LinearMap.id
  calc
    V.ρ x = a • LinearMap.id :=
      Representation.centralCharacter_spec V.ρ (Subgroup.center P.H) le_rfl z
    _ = LinearMap.id := by rw [ha, one_smul]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCentralSector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
