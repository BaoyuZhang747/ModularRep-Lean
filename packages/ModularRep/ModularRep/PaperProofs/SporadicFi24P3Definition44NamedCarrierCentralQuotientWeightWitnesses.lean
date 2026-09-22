import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly

/-! Every sector class has an actual factorizing pair of representatives. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightWitnesses

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

open CentralEllPrimeWeightLocalQuotient
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly

theorem classAt_reindexed_equiv
    {p : ℕ} {K G T : Type u}
    [Field K] [CharZero K] [Group G] [Fintype G]
    (hp : p.Prime) {Q D : RadicalSubgroup (p := p) (G := G)}
    (h : Q = D) (F : T ≃ LocalDefectZeroCharacter (K := K) Q) (x : T) :
    let F' : T ≃ LocalDefectZeroCharacter (K := K) D := by
      rw [h] at F
      exact F
    classAt hp D (F' x) = classAt hp Q (F x) := by
  cases h
  rfl

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

theorem sectorToQuotient_factorising_witness (w : SectorWeights R Z) :
    ∃ (Q : RadicalSubgroup (p := p) (G := X))
      (theta : LocalDefectZeroCharacter (K := K) Q)
      (eta : LocalDefectZeroCharacter (K := K)
        (fixedRadicalImage iota Z hcentral hprimeTo Q)),
      classAt iota.prime Q theta = w.val ∧
      classAt iota.prime
          (fixedRadicalImage iota Z hcentral hprimeTo Q) eta =
        sectorToQuotient iota R Z hcentral hprimeTo OD CU CD
          compatU compatD Sglobal Slocal w ∧
      ∀ x : NormalizerQuotient Q.val,
        theta.val x = eta.val (qW Z Q.val x) := by
  rcases (CE).surjective w with ⟨⟨c, etaD⟩, rfl⟩
  let Q := liftedRepresentative iota Z hcentral hprimeTo Cat c
  have hImage : fixedRadicalImage iota Z hcentral hprimeTo Q = (Catalogue.representative Cat) c :=
    fixedRadicalImage_lift iota Z hcentral hprimeTo ((Catalogue.representative Cat) c)
  let CDi : ∀ eta : LocalDefectZeroCharacter (K := K)
      (fixedRadicalImage iota Z hcentral hprimeTo Q),
      CanonicalRawReduction (quotientRoot iota Z) (characterWeightAt iota.prime
        (fixedRadicalImage iota Z hcentral hprimeTo Q) eta) := by
    rw [hImage]
    exact CD ((Catalogue.representative Cat) c)
  let F := trivialSectorWeightRadicalEquiv
    (R := R) (Z := Z) (Q := Q) (iota := iota)
    (hcentral := hcentral) (hprimeTo := hprimeTo)
    (OD := OD) (CU := CU Q) (CD := CDi)
    (compatU := compatU) (compatD := compatD)
    (Sglobal := Sglobal) (Slocal := Slocal Q)
  let F' : SectorWeightRadicalFibre R Z Q ≃
      LocalDefectZeroCharacter (K := K) ((Catalogue.representative Cat) c) := by
    rw [hImage] at F
    exact F
  let rowW := F'.symm etaD
  have hCE : (CE ⟨c, etaD⟩).val = rowW.val.val := by rfl
  let E0 := sectorLocalToWeight (R := R) (Z := Z) (Q := Q) (iota := iota)
  let t := E0.symm rowW
  let eta := F rowW
  have htheta : classAt iota.prime Q t.val = rowW.val.val := by
    have h := congrArg (fun v : SectorWeightRadicalFibre R Z Q => v.val.val)
      (E0.apply_symm_apply rowW)
    change (localDefectZeroEquivWeightRadicalFibre iota.prime Q t.val).val =
      rowW.val.val at h
    simpa only [localDefectZeroEquivWeightRadicalFibre_apply_val, classAt] using h
  have hcast : classAt iota.prime ((Catalogue.representative Cat) c) (F' rowW) =
      classAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) (F rowW) :=
    classAt_reindexed_equiv iota.prime hImage F rowW
  have heta : classAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta =
      classAt iota.prime ((Catalogue.representative Cat) c) etaD := by
    change classAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) (F rowW) =
      classAt iota.prime ((Catalogue.representative Cat) c) etaD
    rw [← hcast]
    change classAt iota.prime ((Catalogue.representative Cat) c) (F' (F'.symm etaD)) =
      classAt iota.prime ((Catalogue.representative Cat) c) etaD
    exact congrArg (classAt iota.prime ((Catalogue.representative Cat) c))
      (F'.apply_symm_apply etaD)
  refine ⟨Q, t.val, eta, htheta.trans hCE.symm, ?_, ?_⟩
  · exact heta.trans (sectorToQuotient_apply_row iota R Z hcentral hprimeTo OD CU CD
      compatU compatD Sglobal Slocal c etaD).symm
  · let T := trivialSectorRepresentativeEquiv
      (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
      (OU := R.1.operations) (OD := OD) (Q := Q) (CU := CU Q) (CD := CDi)
      (compatU := compatU) (compatD := compatD)
      (Sglobal := Sglobal) (Slocal := Slocal Q)
    have ht : T.symm eta = t := by
      change T.symm (T t) = t
      exact T.symm_apply_apply t
    intro x
    calc
      t.val.val x = (T.symm eta).val.val x :=
        congrArg (fun s => s.val.val x) ht.symm
      _ = eta.val (qW Z Q.val x) :=
        trivialSectorRepresentativeEquiv_symm_character_apply
          (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
          (OU := R.1.operations) (OD := OD) (Q := Q) (CU := CU Q) (CD := CDi)
          (compatU := compatU) (compatD := compatD)
          (Sglobal := Sglobal) (Slocal := Slocal Q) eta x

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightWitnesses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
