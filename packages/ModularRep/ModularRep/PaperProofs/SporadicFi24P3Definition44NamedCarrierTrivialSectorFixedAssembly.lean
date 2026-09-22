import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedUnion
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedRadical

/-! # The downstairs fixed ordinary catalogue combines the original fixed sector -/

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedAssembly

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedUnion

universe u v w
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H
variable {I : Type v} {Row : I → Type w}
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
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

variable (tau : MulAut X) (tauD : MulAut (X ⧸ Z))
variable (square : ∀ x : X, QuotientGroup.mk' Z (tau x) = tauD (QuotientGroup.mk' Z x))

def catalogueSectorFixedEquiv :
    (Σ i : C.FixedIndex tauD, C.FixedLocalRow tauD i) ≃
      {w : SectorWeights R Z // MulOpposite.op tau • w.1 = w.1} := by
  let QI := liftedRepresentative iota Z hcentral hprimeTo C
  have hQ : Function.Bijective (fun i =>
      (Quotient.mk'' (QI i) : RadicalConjugacyClass (p := p) (G := X))) :=
    liftedRepresentative_bijective iota Z hcentral hprimeTo C
  have himage (i : I) : fixedRadicalImage iota Z hcentral hprimeTo (QI i) = C.representative i :=
    fixedRadicalImage_lift iota Z hcentral hprimeTo (C.representative i)
  have CDI : ∀ i : I,
      ∀ eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo (QI i)),
      CanonicalRawReduction (quotientRoot iota Z)
        (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo (QI i)) eta) := by
    intro i
    rw [himage i]
    exact CD i
  have hfix (i : I) : MulOpposite.op tau •
      (Quotient.mk'' (QI i) : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' (QI i) ↔
      MulOpposite.op tauD •
        (Quotient.mk'' (C.representative i) : RadicalConjugacyClass (p := p) (G := X ⧸ Z)) =
          Quotient.mk'' (C.representative i) := by
    have h := fixedRadicalImage_class_fixed_iff iota Z hcentral hprimeTo tau tauD square (QI i)
    rw [himage i] at h
    exact h
  let eIndex : FixedIndex QI tau ≃ C.FixedIndex tauD := Equiv.subtypeEquivRight hfix
  let E : (Σ i : FixedIndex QI tau,
      {w : SectorWeightRadicalFibre R Z (QI i.1) // MulOpposite.op tau • w.1.1 = w.1.1}) ≃
      (Σ i : C.FixedIndex tauD, C.FixedLocalRow tauD i) :=
    Equiv.sigmaCongr eIndex (fun i => fixedSectorRadicalEquivCatalogueRow
      (R := R) (Z := Z) (Q := QI i.1) (iota := iota)
      (hcentral := hcentral) (hprimeTo := hprimeTo) (OD := OD)
      (CU := CU i.1) (CD := CDI i.1) (compatU := compatU) (compatD := compatD)
      (Sglobal := Sglobal) (Slocal := Slocal i.1)
      C tau tauD square (eIndex i) (himage i.1))
  exact E.symm.trans (sectorFixedRadicalUnionEquiv R Z QI hQ tau)

local instance catalogueFixedIndexFintype [Finite I] : Fintype (C.FixedIndex tauD) := Fintype.ofFinite _

include CU CD compatU compatD Sglobal Slocal square in
theorem sectorFixedWeights_card [Fintype I] [∀ i, Finite (Row i)] :
    Nat.card {w : SectorWeights R Z // MulOpposite.op tau • w.1 = w.1} =
      ∑ i : C.FixedIndex tauD, Nat.card (C.FixedLocalRow tauD i) :=
  (Nat.card_congr (catalogueSectorFixedEquiv (R := R) (Z := Z) (iota := iota)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (C := C) (OD := OD) (CU := CU) (CD := CD)
    (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal)
    (tau := tau) (tauD := tauD) (square := square)).symm).trans Nat.card_sigma

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
