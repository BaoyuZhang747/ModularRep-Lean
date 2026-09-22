import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! Actual ordinary local bijections for a correspondence in the specified
trivial sector. Their targets retain the support condition at the original radical. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open CentralEllPrimeIBrFibreTransport CentralEllPrimeWeightLocalQuotient
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

universe u
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

local notation "BF" => trivialBrauerFibre iota R Z hcentral

def brauerAtRadical (eU : BF ≃ SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X)) : Set BF :=
  {phi | radicalClass (eU phi).val =
    (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := X))}

def localOrdinaryRows (Q : RadicalSubgroup (p := p) (G := X)) :
    Set (LocalDefectZeroCharacter (K := K) Q) :=
  {theta | IsCentralCharacterSector Z
    (R.1.operations.ambientBlockData.blockIdempotent
      (R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ)}

def brauerWeightRadicalEquiv (eU : BF ≃ SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X)) :
    brauerAtRadical iota R Z hcentral eU Q ≃ SectorWeightRadicalFibre R Z Q where
  toFun phi := ⟨⟨(eU phi.val).val, phi.property⟩, (eU phi.val).property⟩
  invFun w := ⟨eU.symm ⟨w.val.val, w.property⟩, by
    change radicalClass (eU (eU.symm ⟨w.val.val, w.property⟩)).val = _
    exact (congrArg (fun v : SectorWeights R Z => radicalClass v.val)
      (eU.apply_symm_apply ⟨w.val.val, w.property⟩)).trans w.val.property⟩
  left_inv phi := by
    apply Subtype.ext
    exact eU.symm_apply_apply phi.val
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    change (eU (eU.symm ⟨w.val.val, w.property⟩)).val = w.val.val
    exact congrArg (fun v : SectorWeights R Z => v.val)
      (eU.apply_symm_apply ⟨w.val.val, w.property⟩)

def localOrdinaryEquiv (eU : BF ≃ SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X)) :
    brauerAtRadical iota R Z hcentral eU Q ≃ localOrdinaryRows iota R Z Q :=
  (brauerWeightRadicalEquiv iota R Z hcentral eU Q).trans
    (sectorLocalToWeight (R := R) (Z := Z) (Q := Q) (iota := iota)).symm

omit [Z.Normal] in
theorem localOrdinaryEquiv_class (eU : BF ≃ SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X))
    (phi : brauerAtRadical iota R Z hcentral eU Q) :
    classAt iota.prime Q (localOrdinaryEquiv iota R Z hcentral eU Q phi).val =
      (eU phi.val).val := by
  have h := congrArg (fun w : SectorWeightRadicalFibre R Z Q => w.val.val)
    ((sectorLocalToWeight (R := R) (Z := Z) (Q := Q) (iota := iota)).apply_symm_apply
      (brauerWeightRadicalEquiv iota R Z hcentral eU Q phi))
  change (localDefectZeroEquivWeightRadicalFibre iota.prime Q
      (localOrdinaryEquiv iota R Z hcentral eU Q phi).val).val = (eU phi.val).val at h
  simpa only [localDefectZeroEquivWeightRadicalFibre_apply_val, classAt] using h

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


def localQuotientOrdinaryEquiv (eU : BF ≃ SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X)) :
    brauerAtRadical iota R Z hcentral eU Q ≃
      LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q) :=
  (localOrdinaryEquiv iota R Z hcentral eU Q).trans
    (trivialSectorRepresentativeEquiv (iota := iota) (Z := Z)
      (hcentral := hcentral) (hprimeTo := hprimeTo) (OU := R.1.operations) (OD := OD)
      (Q := Q) (CU := CU Q) (CD := CD (fixedRadicalImage iota Z hcentral hprimeTo Q))
      (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal Q))

theorem localQuotientOrdinaryEquiv_factorisation (eU : BF ≃ SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X))
    (phi : brauerAtRadical iota R Z hcentral eU Q) (x : NormalizerQuotient Q.val) :
    (localOrdinaryEquiv iota R Z hcentral eU Q phi).val.val x =
      (localQuotientOrdinaryEquiv iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eU Q phi).val (qW Z Q.val x) := by
  let L := localOrdinaryEquiv iota R Z hcentral eU Q phi
  let T := trivialSectorRepresentativeEquiv (iota := iota) (Z := Z)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (OU := R.1.operations) (OD := OD)
    (Q := Q) (CU := CU Q) (CD := CD (fixedRadicalImage iota Z hcentral hprimeTo Q))
    (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal Q)
  change L.val.val x = (T L).val (qW Z Q.val x)
  calc
    L.val.val x = (T.symm (T L)).val.val x :=
      congrArg (fun theta => theta.val.val x) (T.symm_apply_apply L).symm
    _ = (T L).val (qW Z Q.val x) := rfl

theorem transported_local_quotient_class (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (Q : RadicalSubgroup (p := p) (G := X))
    (phi : brauerAtRadical iota R Z hcentral
      (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD) Q) :
    classAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q)
      (localQuotientOrdinaryEquiv iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal
        (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD) Q phi) =
      eD ((canonicalBrauerEquiv iota R Z hcentral).symm phi.val) := by
  let eU := transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
  let L := localOrdinaryEquiv iota R Z hcentral eU Q phi
  let eta := localQuotientOrdinaryEquiv iota R Z hcentral hprimeTo OD CU CD compatU compatD
    Sglobal Slocal eU Q phi
  let W := characterWeightAt iota.prime Q L.val
  let U := characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta
  have hW : rawClass W = (eU phi.val).val :=
    localOrdinaryEquiv_class iota R Z hcentral eU Q phi
  let hk := sectorRawKernel iota R Z hcentral hprimeTo CU compatU (eU phi.val) W hW
  have hU : U = rawDescent Z hcentral hprimeTo W hk :=
    rawDescent_unique Z hcentral hprimeTo W hk U rfl
      (localQuotientOrdinaryEquiv_factorisation iota R Z hcentral hprimeTo
        OD CU CD compatU compatD Sglobal Slocal eU Q phi)
  exact (congrArg rawClass hU).trans
    ((sectorToQuotient_apply_raw iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
      (eU phi.val) W hW).symm.trans
        (transportedUp_square iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi.val))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
