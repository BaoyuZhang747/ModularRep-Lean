import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiftedRadicalIndex

/-!
# The downstairs ordinary catalogue combines the original trivial sector

Only the radical indexing is lifted. Original local ordinary characters
are restricted by their specified sector before the sigma union is taken.
-/

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
open SporadicFi24P3Definition44NamedCarrierLiftedRadicalIndex

universe u v w
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H
variable {I : Type v} {Row : I → Type w}

abbrev liftedRepresentative (iota : PrimeRegularRootEmbedding p k K X)
    (Z : Subgroup X) [Z.Normal] (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    (C : Catalogue p K (X ⧸ Z) I Row) (i : I) : RadicalSubgroup (p := p) (G := X) :=
  (fixedRadicalEquiv iota Z hcentral hprimeTo).symm (C.representative i)

omit [CharP k p] [IsAlgClosed k] in
theorem liftedRepresentative_bijective (iota : PrimeRegularRootEmbedding p k K X)
    (Z : Subgroup X) [Z.Normal] (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    (C : Catalogue p K (X ⧸ Z) I Row) : Function.Bijective (fun i =>
      (Quotient.mk'' (liftedRepresentative iota Z hcentral hprimeTo C i) :
        RadicalConjugacyClass (p := p) (G := X))) :=
  liftedRadicalRepresentative_bijective iota Z hcentral hprimeTo C.representative C.radical_bijective

variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]

abbrev SectorWeights :=
  {weight : WeightClass (p := p) (K := K) (X := X) //
    IsCentralCharacterSector Z (R.1.weightBlock weight).1 (1 : Z →* kˣ)}

def sectorRadicalUnionEquiv (Q : I → RadicalSubgroup (p := p) (G := X))
    (hQ : Function.Bijective (fun i => (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X)))) :
    (Σ i : I, SectorWeightRadicalFibre R Z (Q i)) ≃ SectorWeights R Z := by
  let eQ : I ≃ RadicalConjugacyClass (p := p) (G := X) := Equiv.ofBijective _ hQ
  let projection : SectorWeights R Z → RadicalConjugacyClass (p := p) (G := X) := fun w => radicalClass w.1
  let E : (Σ i : I, SectorWeightRadicalFibre R Z (Q i)) ≃
      (Σ c : RadicalConjugacyClass (p := p) (G := X), {w : SectorWeights R Z // projection w = c}) :=
    Equiv.sigmaCongr eQ (fun i => swapNestedSubtype
      (fun w : WeightClass (p := p) (K := K) (X := X) =>
        radicalClass w = (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X)))
      (fun w : WeightClass (p := p) (K := K) (X := X) =>
        IsCentralCharacterSector Z (R.1.weightBlock w).1 (1 : Z →* kˣ)))
  exact E.trans (Equiv.sigmaFiberEquiv projection)

omit [CharP k p] [IsAlgClosed k] [Z.Normal] in
theorem sectorRadicalUnionEquiv_apply (Q : I → RadicalSubgroup (p := p) (G := X))
    (hQ : Function.Bijective (fun i => (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X))))
    (i : I) (w : SectorWeightRadicalFibre R Z (Q i)) :
    (sectorRadicalUnionEquiv R Z Q hQ ⟨i, w⟩).1 = w.1.1 := rfl

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
variable (C : Catalogue p K (X ⧸ Z) I Row)
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (CU : ∀ i (theta : LocalDefectZeroCharacter (K := K)
    (liftedRepresentative iota Z hcentral hprimeTo C i)),
  CanonicalRawReduction iota (characterWeightAt iota.prime
    (liftedRepresentative iota Z hcentral hprimeTo C i) theta))
variable (CD : ∀ i (eta : LocalDefectZeroCharacter (K := K) (C.representative i)),
  CanonicalRawReduction (quotientRoot iota Z) (characterWeightAt iota.prime (C.representative i) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ i, CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' Z) (liftedRepresentative iota Z hcentral hprimeTo C i).1)
  (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo
    (liftedRepresentative iota Z hcentral hprimeTo C i).1
    (liftedRepresentative iota Z hcentral hprimeTo C i).2) iota.prime
  (fixedNormalizer_kernel_central Z (liftedRepresentative iota Z hcentral hprimeTo C i).1 hcentral)
  (fixedNormalizer_kernel_primeTo Z (liftedRepresentative iota Z hcentral hprimeTo C i).1 hcentral hprimeTo))

def catalogueSectorRowEquiv (i : I) :
    Row i ≃ SectorWeightRadicalFibre R Z (liftedRepresentative iota Z hcentral hprimeTo C i) := by
  have hImage : fixedRadicalImage iota Z hcentral hprimeTo
      (liftedRepresentative iota Z hcentral hprimeTo C i) = C.representative i :=
    fixedRadicalImage_lift iota Z hcentral hprimeTo (C.representative i)
  have CDi : ∀ eta : LocalDefectZeroCharacter (K := K)
      (fixedRadicalImage iota Z hcentral hprimeTo (liftedRepresentative iota Z hcentral hprimeTo C i)),
      CanonicalRawReduction (quotientRoot iota Z) (characterWeightAt iota.prime
        (fixedRadicalImage iota Z hcentral hprimeTo (liftedRepresentative iota Z hcentral hprimeTo C i)) eta) := by
    rw [hImage]
    exact CD i
  have E := trivialSectorWeightRadicalEquiv (R := R) (Z := Z)
    (Q := liftedRepresentative iota Z hcentral hprimeTo C i) (iota := iota)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (OD := OD) (CU := CU i) (CD := CDi)
    (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal i)
  have E' : SectorWeightRadicalFibre R Z (liftedRepresentative iota Z hcentral hprimeTo C i) ≃
      LocalDefectZeroCharacter (K := K) (C.representative i) := by
    rw [hImage] at E
    exact E
  exact (C.localEquiv i).trans E'.symm

def catalogueSectorEquiv : (Σ i : I, Row i) ≃ SectorWeights R Z :=
  (Equiv.sigmaCongrRight (fun i => catalogueSectorRowEquiv (R := R) (Z := Z) (iota := iota)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (C := C) (OD := OD) (CU := CU) (CD := CD)
    (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal) i)).trans
      (sectorRadicalUnionEquiv R Z (liftedRepresentative iota Z hcentral hprimeTo C)
        (liftedRepresentative_bijective iota Z hcentral hprimeTo C))

theorem catalogueSectorEquiv_apply (i : I) (r : Row i) :
    (catalogueSectorEquiv (R := R) (Z := Z) (iota := iota)
      (hcentral := hcentral) (hprimeTo := hprimeTo) (C := C) (OD := OD) (CU := CU) (CD := CD)
      (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal) ⟨i, r⟩).1 =
    (catalogueSectorRowEquiv (R := R) (Z := Z) (iota := iota)
      (hcentral := hcentral) (hprimeTo := hprimeTo) (C := C) (OD := OD) (CU := CU) (CD := CD)
      (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal) i r).1.1 := rfl

include CU CD compatU compatD Sglobal Slocal in
theorem sectorWeights_finite [Finite I] [∀ i, Finite (Row i)] : Finite (SectorWeights R Z) :=
  (catalogueSectorEquiv (R := R) (Z := Z) (iota := iota)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (C := C) (OD := OD) (CU := CU) (CD := CD)
    (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal)).finite_iff.mp inferInstance

include CU CD compatU compatD Sglobal Slocal in
theorem sectorWeights_card [Fintype I] [∀ i, Finite (Row i)] :
    Nat.card (SectorWeights R Z) = ∑ i : I, Nat.card (Row i) :=
  (Nat.card_congr (catalogueSectorEquiv (R := R) (Z := Z) (iota := iota)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (C := C) (OD := OD) (CU := CU) (CD := CD)
    (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal)).symm).trans Nat.card_sigma

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
