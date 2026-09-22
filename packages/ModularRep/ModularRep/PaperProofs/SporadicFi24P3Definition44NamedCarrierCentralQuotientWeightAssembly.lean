import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly

/-! The actual quotient weight equivalence with an internally constructed
radical-class index. No finite census or external global map is supplied. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

universe u

def actualRadicalCatalogue
    (p : ℕ) (K G : Type u)
    [Field K] [CharZero K] [Group G] [Fintype G]
    (hp : p.Prime) :
    Catalogue p K G
      (RadicalConjugacyClass (p := p) (G := G))
      (fun c => LocalDefectZeroCharacter (K := K) (Quotient.out c)) where
  prime := hp
  representative := Quotient.out
  radical_bijective := by
    constructor
    · intro a b h
      simpa only [Quotient.out_eq] using h
    · intro c
      exact ⟨c, Quotient.out_eq c⟩
  ordinary := fun _ => id
  ordinary_bijective := fun _ => Function.bijective_id

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (CU : ∀ (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ (Q : RadicalSubgroup (p := p) (G := X ⧸ Z))
    (eta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction (quotientRoot iota Z) (characterWeightAt iota.prime Q eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ Q : RadicalSubgroup (p := p) (G := X),
  CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' Z) Q.1)
    (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
    (fixedNormalizer_kernel_central Z Q.1 hcentral)
    (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))

local notation "Cat" => actualRadicalCatalogue p K (X ⧸ Z) iota.prime
local notation "CE" => catalogueSectorEquiv
  (R := R) (Z := Z) (iota := iota)
  (hcentral := hcentral) (hprimeTo := hprimeTo) (C := Cat) (OD := OD)
  (CU := fun c => CU (liftedRepresentative iota Z hcentral hprimeTo Cat c))
  (CD := fun c => CD ((Catalogue.representative Cat) c))
  (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal)
  (Slocal := fun c => Slocal (liftedRepresentative iota Z hcentral hprimeTo Cat c))

def sectorToQuotient :
    SectorWeights R Z ≃ ConjugacyClass (p := p) (K := K) (G := X ⧸ Z) :=
  (CE).symm.trans (Cat).globalEquiv

theorem sectorToQuotient_apply_row
    (c : RadicalConjugacyClass (p := p) (G := X ⧸ Z))
    (eta : LocalDefectZeroCharacter (K := K) (Quotient.out c)) :
    sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
        (CE ⟨c, eta⟩) = classAt iota.prime (Quotient.out c) eta := by
  change (Cat).globalEquiv ((CE).symm (CE ⟨c, eta⟩)) = _
  rw [(CE).symm_apply_apply]
  exact (Cat).globalEquiv_apply ⟨c, eta⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
