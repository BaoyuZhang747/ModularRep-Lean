import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorSplit
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! Literal disjoint-union carriers; the underlying characters never change. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorCarriers

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

omit [CharP k p] in
theorem centerSupport_iff (w : W) :
    IsCentralCharacterSector C (R.1.weightBlock w).val (1 : C →* kˣ) ↔
      weightSector (R := R) w = 1 := by
  constructor
  · intro h
    exact ((R.1.weightBlock w).property.centralCharacterSector_unique C le_rfl h).symm
  · intro h
    have hs := (R.1.weightBlock w).property.centralCharacterSector_isSector C le_rfl
    change IsCentralCharacterSector C (R.1.weightBlock w).val (weightSector (R := R) w) at hs
    rwa [h] at hs

def centerWeightFibreEquiv : SW ≃ {w : W // weightSector (R := R) w = 1} :=
  Equiv.subtypeEquivRight (centerSupport_iff R)

def faithfulBrauerComplementEquiv (hprime : (Nat.card C).Prime) :
    FB ≃ {phi : IBr iota // brauerSector iota hinj blocks phi ≠ 1} where
  toFun phi := ⟨phi.val, (injective_iff_ne_one_of_prime_card hprime _).mp phi.faithful⟩
  invFun phi := ⟨phi.val, (injective_iff_ne_one_of_prime_card hprime _).mpr phi.property⟩
  left_inv phi := by cases phi; rfl
  right_inv phi := rfl

def faithfulWeightComplementEquiv (hprime : (Nat.card C).Prime) :
    FW ≃ {w : W // weightSector (R := R) w ≠ 1} where
  toFun w := ⟨w.val, (injective_iff_ne_one_of_prime_card hprime _).mp w.faithful⟩
  invFun w := ⟨w.val, (injective_iff_ne_one_of_prime_card hprime _).mpr w.property⟩
  left_inv w := by cases w; rfl
  right_inv w := rfl

def brauerUnion (hprime : (Nat.card C).Prime) : TB ⊕ FB ≃ IBr iota := by
  classical
  exact (Equiv.sumCongr (Equiv.refl TB)
    (faithfulBrauerComplementEquiv iota hinj blocks R E1 hprime)).trans
      (Equiv.sumCompl (fun phi : IBr iota => brauerSector iota hinj blocks phi = 1))

def weightUnion (hprime : (Nat.card C).Prime) : SW ⊕ FW ≃ W := by
  classical
  exact (Equiv.sumCongr (centerWeightFibreEquiv R)
    (faithfulWeightComplementEquiv iota hinj blocks R E1 hprime)).trans
      (Equiv.sumCompl (fun w : W => weightSector (R := R) w = 1))

theorem brauerUnion_inl (hprime : (Nat.card C).Prime) (phi : TB) :
    brauerUnion iota hinj blocks R E1 hprime (Sum.inl phi) = phi.val := rfl

theorem brauerUnion_inr (hprime : (Nat.card C).Prime) (phi : FB) :
    brauerUnion iota hinj blocks R E1 hprime (Sum.inr phi) = phi.val := rfl

theorem weightUnion_inl (hprime : (Nat.card C).Prime) (w : SW) :
    weightUnion iota hinj blocks R E1 hprime (Sum.inl w) = w.val := rfl

theorem weightUnion_inr (hprime : (Nat.card C).Prime) (w : FW) :
    weightUnion iota hinj blocks R E1 hprime (Sum.inr w) = w.val := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
