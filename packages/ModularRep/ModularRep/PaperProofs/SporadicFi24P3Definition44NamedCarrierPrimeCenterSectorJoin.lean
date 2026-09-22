import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorCarriers

/-! Join the two retained maps on literal carriers, without selecting a new family. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorJoin

open ModularRep Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorSplit

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "C" => Subgroup.center G
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "TB" => Fibre (brauerSector iota hinj blocks) (1 : CentralSector (k := k) (X := G))
local notation "W" => CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)
local notation "SW" => SectorWeights R C


open SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorCarriers
variable (hprime : (Nat.card (Subgroup.center G)).Prime)
variable (eT : Fibre (brauerSector iota hinj blocks) (1 : CentralSector (k := k) (X := G)) ≃
  SectorWeights R (Subgroup.center G))
variable (eF : FaithfulIBr iota hinj blocks R E1 ≃ FaithfulWeight iota hinj blocks R E1)
local notation "BU" => brauerUnion iota hinj blocks R E1 hprime
local notation "WU" => weightUnion iota hinj blocks R E1 hprime

def joined : IBr iota ≃ W :=
  (BU).symm.trans ((Equiv.sumCongr eT eF).trans WU)

local notation "J" => joined iota hinj blocks R E1 hprime eT eF

theorem joined_trivial (phi : TB) : J phi.val = (eT phi).val := by
  have h : (BU).symm phi.val = Sum.inl phi := (BU).symm_apply_apply (Sum.inl phi)
  change WU ((Equiv.sumCongr eT eF) ((BU).symm phi.val)) = _
  rw [h]
  rfl

theorem joined_faithful (phi : FB) : J phi.val = (eF phi).val := by
  have h : (BU).symm phi.val = Sum.inr phi := (BU).symm_apply_apply (Sum.inr phi)
  change WU ((Equiv.sumCongr eT eF) ((BU).symm phi.val)) = _
  rw [h]
  rfl

theorem joined_equivariant
    (hT : ∀ (a : (MulAut G)ᵐᵒᵖ) (phi psi : TB), psi.val = a • phi.val →
      (eT psi).val = a • (eT phi).val)
    (hF : ∀ (a : (MulAut G)ᵐᵒᵖ) (phi : FB), eF (a • phi) = a • eF phi)
    (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota) : J (a • phi) = a • J phi := by
  by_cases hphi : brauerSector iota hinj blocks phi = 1
  · let t : TB := ⟨phi, hphi⟩
    let ta : TB := ⟨a • phi, by
      rw [brauerSector_equivariant iota hinj blocks E1, hphi, centralSector_smul_one]⟩
    change J ta.val = a • J t.val
    rw [joined_trivial, joined_trivial]
    exact hT a t ta rfl
  · let f : FB := ⟨phi, (injective_iff_ne_one_of_prime_card hprime _).mpr hphi⟩
    change J (a • f).val = a • J f.val
    rw [joined_faithful, joined_faithful]
    exact congrArg (fun w : FW => w.val) (hF a f)

theorem joined_block
    (hT : ∀ phi : TB, R.1.weightBlock (eT phi).val = brauerBlock iota hinj blocks phi.val)
    (hF : ∀ phi : FB, R.1.weightBlock (eF phi).val = brauerBlock iota hinj blocks phi.val)
    (phi : IBr iota) : R.1.weightBlock (J phi) = brauerBlock iota hinj blocks phi := by
  by_cases hphi : brauerSector iota hinj blocks phi = 1
  · let t : TB := ⟨phi, hphi⟩
    change R.1.weightBlock (J t.val) = _
    rw [joined_trivial]
    exact hT t
  · let f : FB := ⟨phi, (injective_iff_ne_one_of_prime_card hprime _).mpr hphi⟩
    change R.1.weightBlock (J f.val) = _
    rw [joined_faithful]
    exact hF f

theorem joined_sector
    (hT : ∀ phi : TB, R.1.weightBlock (eT phi).val = brauerBlock iota hinj blocks phi.val)
    (hF : ∀ phi : FB, R.1.weightBlock (eF phi).val = brauerBlock iota hinj blocks phi.val)
    (phi : IBr iota) : weightSector (R := R) (J phi) = brauerSector iota hinj blocks phi := by
  unfold weightSector brauerSector
  rw [joined_block iota hinj blocks R E1 hprime eT eF hT hF]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
