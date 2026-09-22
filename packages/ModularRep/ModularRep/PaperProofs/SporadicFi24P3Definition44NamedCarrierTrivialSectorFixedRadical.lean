import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalFixedCorrection
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPairedInnerCorrection
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly

/-! # Each original fixed sector fibre is the canonical downstairs fixed row -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedRadical

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierLocalFixedCorrection
open SporadicFi24P3Definition44NamedCarrierPairedInnerCorrection
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
open TypeBCentralKernelNormalizerInertia

universe u v w

def fixedLocalCastEquiv
    {p : ℕ} {K H : Type u} [Field K] [CharZero K] [Group H] [Fintype H]
    (Q Q' : CharacterWeight.RadicalSubgroup (p := p) (G := H)) (h : Q = Q')
    (alpha : MulAut H)
    (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (stable' : Q'.1.comap alpha.toMonoidHom = Q'.1) :
    {theta : LocalDefectZeroCharacter (K := K) Q //
      OrdinaryIrreducibleCharacter.twist K _ theta.1 (localAut Q.1 alpha stable) = theta.1} ≃
    {theta : LocalDefectZeroCharacter (K := K) Q' //
      OrdinaryIrreducibleCharacter.twist K _ theta.1 (localAut Q'.1 alpha stable') = theta.1} := by
  cases h
  exact Equiv.refl _

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal]
variable [Invertible (Fintype.card Z : k)]
variable (Q : RadicalSubgroup (p := p) (G := X))

variable (iota : PrimeRegularRootEmbedding p k K X)

variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q),
  CanonicalRawReduction (quotientRoot iota Z)
    (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' Z) Q.1)
  (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
  (fixedNormalizer_kernel_central Z Q.1 hcentral)
  (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))

def fixedSectorRadicalEquivCatalogueRow
    {I : Type v} {Row : I → Type w} (C : Catalogue p K (X ⧸ Z) I Row)
    (tau : MulAut X) (tauD : MulAut (X ⧸ Z))
    (square : ∀ x : X, QuotientGroup.mk' Z (tau x) = tauD (QuotientGroup.mk' Z x))
    (i : C.FixedIndex tauD)
    (himage : fixedRadicalImage iota Z hcentral hprimeTo Q = C.representative i.1) :
    {w : SectorWeightRadicalFibre R Z Q // MulOpposite.op tau • w.1.1 = w.1.1} ≃
      C.FixedLocalRow tauD i := by
  classical
  let f := QuotientGroup.mk' Z
  let Qbar := fixedRadicalImage iota Z hcentral hprimeTo Q
  have hfixedD : MulOpposite.op tauD •
      (Quotient.mk'' Qbar : RadicalConjugacyClass (p := p) (G := X ⧸ Z)) = Quotient.mk'' Qbar := by
    simpa only [Qbar, himage] using i.2
  have hfixedU := (fixedRadicalImage_class_fixed_iff
    iota Z hcentral hprimeTo tau tauD square Q).mpr hfixedD
  have hex := exists_compatible_innerCorrection f tau tauD square Q hfixedU
  let g : X := Classical.choose hex
  let sigma := tau * MulAut.conj g
  let beta := tauD * MulAut.conj (f g)
  have stableU : Q.1.comap sigma.toMonoidHom = Q.1 := (Classical.choose_spec hex).1
  have correctedSquare : ∀ x : X, f (sigma x) = beta (f x) := (Classical.choose_spec hex).2.2
  have stableImage : Qbar.1.comap beta.toMonoidHom = Qbar.1 :=
    image_stable f sigma beta correctedSquare Q.1 stableU
  have stableC : (C.representative i.1).1.comap beta.toMonoidHom = (C.representative i.1).1 := by
    simpa only [Qbar, himage] using stableImage
  let Echange :
      {w : SectorWeightRadicalFibre R Z Q // MulOpposite.op tau • w.1.1 = w.1.1} ≃
      {w : SectorWeightRadicalFibre R Z Q // MulOpposite.op sigma • w.1.1 = w.1.1} :=
    Equiv.subtypeEquivRight (fun _ => by simp only [sigma, innerCorrection_weight_smul])
  let E1 := trivialSectorWeightRadicalFixedEquiv
    (R := R) (Z := Z) (Q := Q) (iota := iota) (hcentral := hcentral) (hprimeTo := hprimeTo)
    (OD := OD) (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
    (Sglobal := Sglobal) (Slocal := Slocal)
    (sigma := sigma) (beta := beta) (square := correctedSquare) (stableU := stableU)
  let Ecast := fixedLocalCastEquiv (K := K) Qbar (C.representative i.1) himage beta stableImage stableC
  let Ecompare :
      {eta : LocalDefectZeroCharacter (K := K) (C.representative i.1) //
        OrdinaryIrreducibleCharacter.twist K _ eta.1
          (localAut (C.representative i.1).1 beta stableC) = eta.1} ≃
      {eta : LocalDefectZeroCharacter (K := K) (C.representative i.1) //
        OrdinaryIrreducibleCharacter.twist K _ eta.1
          (localAut (C.representative i.1).1 (C.correctedAut tauD i) (C.correctedStable tauD i)) = eta.1} :=
    Equiv.subtypeEquivRight (fun eta =>
      local_fixed_iff_of_innerCorrections C.prime (C.representative i.1) tauD
        (f g) (C.correctionElement tauD i) stableC (C.correctedStable tauD i) eta)
  let Erows : C.FixedLocalRow tauD i ≃
      {eta : LocalDefectZeroCharacter (K := K) (C.representative i.1) //
        OrdinaryIrreducibleCharacter.twist K _ eta.1
          (localAut (C.representative i.1).1 (C.correctedAut tauD i) (C.correctedStable tauD i)) = eta.1} :=
    (C.localEquiv i.1).subtypeEquiv (fun _ => Iff.rfl)
  exact Echange.trans (E1.trans (Ecast.trans (Ecompare.trans Erows.symm)))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedRadical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
