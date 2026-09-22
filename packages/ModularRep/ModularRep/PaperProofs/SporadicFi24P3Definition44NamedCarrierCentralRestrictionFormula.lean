import ModularRep.CharacterWeightCentralRestriction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCentralSector
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralRootLift
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence

/-!
# Ordinary central restriction detects the specified weight sector

The scalar is computed using the same retained root convention as the
canonical reduction. Nonzero degree permits cancellation in characteristic
zero; root injectivity is used only on prime regular central values.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralRestrictionFormula

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
open SporadicFi24P3Definition44NamedCarrierLocalCentralSector
open SporadicFi24P3Definition44NamedCarrierCentralRootLift

universe u

local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H := Fintype.ofFinite H

theorem irreducible_finrank_pos
    {k G M : Type*} [Field k] [Group G]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (rho : Representation k G M) [rho.IsIrreducible] :
    0 < Module.finrank k M := by
  let _ : Nontrivial rho.asModule := IsSimpleModule.nontrivial k[G] rho.asModule
  let _ : Nontrivial M := rho.asModuleEquiv.symm.toEquiv.nontrivial
  exact Module.finrank_pos

theorem root_lift_one
    {p : ℕ} {k K G : Type*}
    [Field k] [Field K] [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) :
    iota.lift (1 : k) = (1 : K) := by
  simpa [PrimeRegularRootEmbedding.liftRoot] using
    iota.lift_coe (1 : rootsOfUnity (primeRegularExponent p G) k)

theorem brauer_value_one
    {p : ℕ} {k K G M : Type*}
    [Field k] [Field K] [Group G] [Finite G]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (rho : Representation k G M) [rho.IsIrreducible]
    (iota : PrimeRegularRootEmbedding p k K G) :
    rho.brauerCharacterOfRootEmbedding iota ⟨1, isPrimeRegular_one⟩ =
      (Module.finrank k M : K) := by
  simpa [root_lift_one] using
    rho.brauerCharacterOfRootEmbedding_apply_central
      iota (Subgroup.center G) le_rfl 1 isPrimeRegular_one

theorem centralCharacter_mem_charpoly_roots
    {k G M : Type*}
    [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (rho : Representation k G M) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (z : Z) :
    (rho.centralCharacter Z hZ z : k) ∈ (rho (z : G)).charpoly.roots := by
  rw [rho.centralCharacter_spec Z hZ z, Representation.roots_charpoly_smul_id]
  exact Multiset.mem_replicate.mpr ⟨(irreducible_finrank_pos rho).ne', rfl⟩

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

theorem localCharacter_one_eq_finrank_of_reduction
    (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X) (source : CanonicalRawReduction iota W) :
    W.localCharacter 1 =
      (Module.finrank k (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V : K) := by
  let rhoN := (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
  let _ : Representation.IsIrreducible rhoN := (Classical.choose_spec source.localBrauer.2).1
  calc
    W.localCharacter 1 = source.localBrauer.1 ⟨1, isPrimeRegular_one⟩ :=
      source.localBrauer_reduction ⟨1, isPrimeRegular_one⟩
    _ = _ := by
      rw [chosenIBrRepresentation_character]
      exact brauer_value_one rhoN source.normalizerRoot

theorem localCharacter_one_ne_zero_of_reduction
    (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X) (source : CanonicalRawReduction iota W) :
    W.localCharacter 1 ≠ 0 := by
  let rhoN := (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
  let _ : Representation.IsIrreducible rhoN := (Classical.choose_spec source.localBrauer.2).1
  rw [localCharacter_one_eq_finrank_of_reduction iota W source]
  exact Nat.cast_ne_zero.mpr (irreducible_finrank_pos rhoN).ne'

variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem centralRestriction_eq_degree_mul_rawWeightSector_lift
    (iota : PrimeRegularRootEmbedding p k K X)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (W : CharacterWeight p K X) (source : CanonicalRawReduction iota W)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (z : Subgroup.center X) :
    CharacterWeight.centralRestriction W z = W.localCharacter 1 *
      iota.lift (blockSector (R.1.operations.rawWeightBlock W) z : k) := by
  let N := Subgroup.normalizer (W.subgroup : Set X)
  let Z := Subgroup.center X
  let rhoN : Representation k N
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V :=
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
  let _ : rhoN.IsIrreducible := (Classical.choose_spec source.localBrauer.2).1
  have hZN : Z ≤ N := Subgroup.center_le_normalizer (W.subgroup : Set X)
  let zN : N := ⟨z.1, hZN z.2⟩
  let zNZ : Z.subgroupOf N := ⟨zN, z.2⟩
  have hprimeTo : ¬ p ∣ Nat.card Z := by
    intro hdiv
    apply Invertible.ne_zero (Fintype.card Z : k)
    exact (CharP.cast_eq_zero_iff k p (Fintype.card Z)).mpr
      (by simpa only [Nat.card_eq_fintype_card] using hdiv)
  have hzZ : IsPrimeRegular p z :=
    IsPrimeRegular.of_coprime_natCard
      (iota.prime.coprime_iff_not_dvd.mpr hprimeTo).symm z
  have hzN : IsPrimeRegular p zN := hzZ.map (Subgroup.inclusion hZN)
  let a : k := (rhoN.centralCharacter (Z.subgroupOf N)
    (subgroupOf_le_center N Z le_rfl) zNZ : k)
  have hscalar : a = (blockSector (R.1.operations.rawWeightBlock W) z : k) := by
    exact congrArg (fun mu : Z.subgroupOf N →* kˣ => (mu zNZ : k))
      (rawWeightBlock_local_centralCharacter iota R W source compatibility)
  have hrootmem : a ∈ (rhoN zN).charpoly.roots :=
    centralCharacter_mem_charpoly_roots rhoN (Z.subgroupOf N)
      (subgroupOf_le_center N Z le_rfl) zNZ
  let zeta : rootsOfUnity (primeRegularExponent p N) k :=
    rhoN.charpolyRootAsRootOfUnity source.normalizerRoot ⟨zN, hzN⟩ ⟨a, hrootmem⟩
  have hzeta : ((zeta : kˣ) : k) = a := rfl
  have hroots : source.normalizerRoot = subgroupRoot iota N :=
    source.normalizerRoot_eq.trans (normalizerRootAt_eq_subgroupRoot iota W)
  have hlift : source.normalizerRoot.lift a = iota.lift a := by
    calc
      source.normalizerRoot.lift a = (subgroupRoot iota N).lift a :=
        congrArg (fun root : PrimeRegularRootEmbedding p k K N => root.lift a) hroots
      _ = iota.lift a := by
        simpa only [hzeta] using subgroupRoot_lift_coe iota N zeta
  have hN1 : W.localCharacter 1 =
      (Module.finrank k (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V : K) :=
    localCharacter_one_eq_finrank_of_reduction iota W source
  change W.localCharacter (QuotientGroup.mk zN) = W.localCharacter 1 *
    iota.lift (blockSector (R.1.operations.rawWeightBlock W) z : k)
  calc
    W.localCharacter (QuotientGroup.mk zN) = source.localBrauer.1 ⟨zN, hzN⟩ :=
      source.localBrauer_reduction ⟨zN, hzN⟩
    _ = rhoN.brauerCharacterOfRootEmbedding source.normalizerRoot ⟨zN, hzN⟩ :=
      congrArg (fun chi : PrimeRegularClassFunction K N p => chi ⟨zN, hzN⟩)
        (chosenIBrRepresentation_character source.normalizerRoot source.localBrauer)
    _ = (Module.finrank k
        (chosenIBrRepresentation source.normalizerRoot source.localBrauer).V : K) *
        source.normalizerRoot.lift a :=
      rhoN.brauerCharacterOfRootEmbedding_apply_central source.normalizerRoot
        (Z.subgroupOf N) (subgroupOf_le_center N Z le_rfl) zNZ hzN
    _ = _ := by rw [hlift, hscalar, ← hN1]

theorem centralRestriction_eq_degree_mul_lift_iff_rawWeightSector_eq
    (iota : PrimeRegularRootEmbedding p k K X)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (W : CharacterWeight p K X) (source : CanonicalRawReduction iota W)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (nu : Subgroup.center X →* kˣ) :
    (∀ z : Subgroup.center X, CharacterWeight.centralRestriction W z =
      W.localCharacter 1 * iota.lift (nu z : k)) ↔
      blockSector (R.1.operations.rawWeightBlock W) = nu := by
  constructor
  · intro h
    apply centralRootLift_injective iota
    funext z
    exact mul_left_cancel₀ (localCharacter_one_ne_zero_of_reduction iota W source)
      ((centralRestriction_eq_degree_mul_rawWeightSector_lift
        iota R W source compatibility z).symm.trans (h z))
  · intro h z
    rw [centralRestriction_eq_degree_mul_rawWeightSector_lift iota R W source compatibility z, h]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralRestrictionFormula


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
