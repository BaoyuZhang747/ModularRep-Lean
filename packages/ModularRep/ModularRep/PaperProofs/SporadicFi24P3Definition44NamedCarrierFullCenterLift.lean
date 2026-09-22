import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCenterScalar
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence

/-! The ordinary normalizer lift lies over the same character of the full
centre. Scalar equality comes from actual block induction, and root-lift
agreement is used only on actual eigenvalues in the canonical convention. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCenterLift

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCenterScalar

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

private theorem irreducible_finrank_pos
    {k G M : Type*} [Field k] [Group G]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (rho : Representation k G M) [rho.IsIrreducible] :
    0 < Module.finrank k M := by
  let : Nontrivial rho.asModule := IsSimpleModule.nontrivial k[G] rho.asModule
  let : Nontrivial M := rho.asModuleEquiv.symm.toEquiv.nontrivial
  exact Module.finrank_pos

private theorem root_lift_one {p : ℕ} {k K G : Type*}
    [Field k] [Field K] [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) : iota.lift (1 : k) = (1 : K) := by
  simpa [PrimeRegularRootEmbedding.liftRoot] using
    iota.lift_coe (1 : rootsOfUnity (primeRegularExponent p G) k)

private theorem brauer_value_one {p : ℕ} {k K G M : Type*}
    [Field k] [Field K] [Group G] [Finite G]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (rho : Representation k G M) [rho.IsIrreducible]
    (iota : PrimeRegularRootEmbedding p k K G) :
    rho.brauerCharacterOfRootEmbedding iota ⟨1, isPrimeRegular_one⟩ =
      (Module.finrank k M : K) := by
  simpa [root_lift_one] using rho.brauerCharacterOfRootEmbedding_apply_central
    iota (Subgroup.center G) le_rfl 1 isPrimeRegular_one

private theorem centralCharacter_mem_charpoly_roots
    {k G M : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (rho : Representation k G M) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (z : Z) :
    (rho.centralCharacter Z hZ z : k) ∈ (rho (z : G)).charpoly.roots := by
  rw [rho.centralCharacter_spec Z hZ z, Representation.roots_charpoly_smul_id]
  exact Multiset.mem_replicate.mpr ⟨(irreducible_finrank_pos rho).ne', rfl⟩

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H) (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))

include source compatibility hrawBlock hcenter in
theorem full_center_character_value
    (lambda : OrdinaryIrreducibleCharacter.Irr P.K (Subgroup.center P.H))
    (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
      psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩ * lambda z.1)
    (z : Subgroup.center P.H) :
    V.localCharacter (QuotientGroup.mk
      (⟨z.1, Subgroup.center_le_normalizer (V.subgroup : Set P.H) z.2⟩ :
        Subgroup.normalizer (V.subgroup : Set P.H))) = V.localCharacter 1 * lambda z := by
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let Z := Subgroup.center P.H
  let rhoN : Representation P.k N (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V :=
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
  let rhoG : Representation P.k P.H (chosenBrauerRepresentation P psi).V :=
    (chosenBrauerRepresentation P psi).ρ
  let : rhoN.IsIrreducible := (Classical.choose_spec source.localBrauer.2).1
  let : rhoG.IsIrreducible := chosenBrauerRepresentation_irreducible P psi
  have hZN : Z ≤ N := Subgroup.center_le_normalizer (V.subgroup : Set P.H)
  let zN : N := ⟨z.1, hZN z.2⟩
  let zNZ : Z.subgroupOf N := ⟨zN, z.2⟩
  have hzZ : IsPrimeRegular P.p z :=
    IsPrimeRegular.of_coprime_natCard
      (P.iota.prime.coprime_iff_not_dvd.mpr hcenter).symm z
  have hzG : IsPrimeRegular P.p z.1 := hzZ.map Z.subtype
  have hzN : IsPrimeRegular P.p zN := hzZ.map (Subgroup.inclusion hZN)
  let a : P.k := (rhoG.centralCharacter Z le_rfl z : P.k)
  have hscalar : (rhoN.centralCharacter (Z.subgroupOf N) (subgroupOf_le_center N Z le_rfl) zNZ : P.k) = a := by
    exact congrArg Units.val (full_center_scalar_eq P psi V source compatibility hrawBlock hcenter zNZ)
  have hlift : source.normalizerRoot.lift a = P.iota.lift a :=
    canonicalNormalizerRoot_compatible P.iota V source rhoG ⟨zN, hzN⟩
      ⟨a, centralCharacter_mem_charpoly_roots rhoG Z le_rfl z⟩
  have hG : psi.1.1 (PrimeRegularElement.map Z.subtype ⟨z, hzZ⟩) =
      (Module.finrank P.k (chosenBrauerRepresentation P psi).V : P.K) * P.iota.lift a := by
    rw [chosenBrauerRepresentation_character]
    exact rhoG.brauerCharacterOfRootEmbedding_apply_central P.iota Z le_rfl z hzG
  have hG1 : psi.1.1 ⟨1, isPrimeRegular_one⟩ =
      (Module.finrank P.k (chosenBrauerRepresentation P psi).V : P.K) := by
    rw [chosenBrauerRepresentation_character]
    exact brauer_value_one rhoG P.iota
  have hdim : (Module.finrank P.k (chosenBrauerRepresentation P psi).V : P.K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (irreducible_finrank_pos rhoG).ne'
  have hlambda : P.iota.lift a = lambda z := by
    apply mul_left_cancel₀ hdim
    exact hG.symm.trans ((hglobal ⟨z, hzZ⟩).trans (congrArg (fun d => d * lambda z) hG1))
  have hN1 : V.localCharacter 1 =
      (Module.finrank P.k (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V : P.K) := by
    calc
      V.localCharacter 1 = source.localBrauer.1 ⟨1, isPrimeRegular_one⟩ :=
        source.localBrauer_reduction ⟨1, isPrimeRegular_one⟩
      _ = _ := by
        rw [chosenIBrRepresentation_character]
        exact brauer_value_one rhoN source.normalizerRoot
  calc
    V.localCharacter (QuotientGroup.mk zN) = source.localBrauer.1 ⟨zN, hzN⟩ :=
      source.localBrauer_reduction ⟨zN, hzN⟩
    _ = rhoN.brauerCharacterOfRootEmbedding source.normalizerRoot ⟨zN, hzN⟩ :=
      congrArg (fun chi : PrimeRegularClassFunction P.K N P.p => chi ⟨zN, hzN⟩)
        (chosenIBrRepresentation_character source.normalizerRoot source.localBrauer)
    _ = (Module.finrank P.k (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V : P.K) *
        source.normalizerRoot.lift
          (rhoN.centralCharacter (Z.subgroupOf N) (subgroupOf_le_center N Z le_rfl) zNZ : P.k) :=
      rhoN.brauerCharacterOfRootEmbedding_apply_central source.normalizerRoot
        (Z.subgroupOf N) (subgroupOf_le_center N Z le_rfl) zNZ hzN
    _ = V.localCharacter 1 * lambda z := by rw [hscalar, hlift, hlambda, ← hN1]

include source compatibility hrawBlock hcenter in
theorem exists_ordinary_lift_over_full_center :
    ∃ thetaHat : OrdinaryIrreducibleCharacter.Irr P.K (Subgroup.normalizer (V.subgroup : Set P.H)),
      (∀ n, thetaHat n = V.localCharacter (QuotientGroup.mk n)) ∧
      ∀ lambda : OrdinaryIrreducibleCharacter.Irr P.K (Subgroup.center P.H),
        (∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
          psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
            psi.1.1 ⟨1, isPrimeRegular_one⟩ * lambda z.1) →
        ∀ z : Subgroup.center P.H,
          thetaHat ⟨z.1, Subgroup.center_le_normalizer (V.subgroup : Set P.H) z.2⟩ =
            thetaHat 1 * lambda z := by
  refine ⟨inflateOrdinaryCharacter
    (V.subgroup.subgroupOf (Subgroup.normalizer (V.subgroup : Set P.H))) V.localCharacter,
    fun _ => rfl, ?_⟩
  intro lambda hglobal z
  exact full_center_character_value P psi V source compatibility hrawBlock hcenter lambda hglobal z

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCenterLift


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
