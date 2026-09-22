import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientImageSector
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction

/-!
# The whole trivial-sector local row through the central quotient

Kernel constancy is equivalent to the actual induced block's trivial
central support. Literal inflation consequently covers every downstairs
local defect-zero character, without selecting an ambient block.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient

open ModularRep ModularRep.CharacterWeight
open ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryEquiv
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToLocalOrdinaryEquiv
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
open SporadicFi24P3Definition44NamedCarrierFixedCentralCharacterKernel
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralWeightBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierQuotientImageSector
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction
open CentralEllPrimeWeightLocalQuotient TypeBCentralKernelNormalizerInertia

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H

variable (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
variable [Invertible (Fintype.card Z : k)]
variable {BlockU BlockD : Type u}
variable [MulAction (MulAut X)ᵐᵒᵖ BlockU] [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OU : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X) (Block := BlockU))
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (Q : RadicalSubgroup (p := p) (G := X))
variable (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q),
  CanonicalRawReduction (quotientRoot iota Z)
    (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota OU)
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

include CU CD compatU compatD Sglobal Slocal in
theorem rawBlock_trivialSector_iff_kernel (theta : LocalDefectZeroCharacter (K := K) Q) :
    IsCentralCharacterSector Z (OU.ambientBlockData.blockIdempotent
      (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ) ↔
      ∀ x : (qW Z Q.1).ker, theta.1 (x : NormalizerQuotient Q.1) = theta.1 1 := by
  classical
  let _ : Fact p.Prime := ⟨iota.prime⟩
  constructor
  · intro hsector
    exact fixedZ_character_constant_on_qW_kernel iota OU
      (characterWeightAt iota.prime Q theta) (CU theta) compatU Z
      hcentral hprimeTo hsector.mul_eq_self
  · intro hkernel
    let Qbar := fixedRadicalImage iota Z hcentral hprimeTo Q
    let D := KernelConstantDefectZeroIrr (p := p) (K := K) (qW Z Q.1)
    let E : D ≃ LocalDefectZeroCharacter (K := K) Qbar :=
      qWDefectZeroEquiv Z hcentral hprimeTo Q.1 Q.2
    let t : D := ⟨theta, hkernel⟩
    let eta := E t
    have hfactor : theta.1.1 = fun x : NormalizerQuotient Q.1 => eta.1 (qW Z Q.1 x) :=
      descendCharacter_factorisation (qW Z Q.1)
        (qW_surjective_ofNavarroTiep Z hcentral hprimeTo Q.1 Q.2
          (fixedCentralQuotientSource Z hcentral hprimeTo Q.1 Q.2)) theta.1 hkernel
    have himage : algebraMapOf (QuotientGroup.mk' Z)
        (OU.ambientBlockData.blockIdempotent
          (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) =
        OD.ambientBlockData.blockIdempotent
          (OD.rawWeightBlock (characterWeightAt iota.prime Qbar eta)) :=
      rawWeightBlock_image iota Z Q Qbar.2 theta eta (CU theta) (CD eta) hfactor
        hcentral hprimeTo OU OD compatU compatD Sglobal Slocal
    let _ := OU.ambientBlockData.fintypeBlock
    let _ := OD.ambientBlockData.fintypeBlock
    have hne : algebraMapOf (QuotientGroup.mk' Z)
        (OU.ambientBlockData.blockIdempotent
          (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) ≠ 0 := by
      rw [himage]
      exact (OD.ambientBlockData.blocks.primitive
        (OD.rawWeightBlock (characterWeightAt iota.prime Qbar eta))).ne_zero
    exact trivial_sector_of_quotient_image_ne_zero Z hcentral
      (OU.ambientBlockData.blocks.primitive
        (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) hne

def trivialSectorRepresentativeEquiv :
    {theta : LocalDefectZeroCharacter (K := K) Q //
      IsCentralCharacterSector Z (OU.ambientBlockData.blockIdempotent
        (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ)} ≃
      LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q) := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  let E0 : {theta : LocalDefectZeroCharacter (K := K) Q //
      IsCentralCharacterSector Z (OU.ambientBlockData.blockIdempotent
        (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ)} ≃
      KernelConstantDefectZeroIrr (p := p) (K := K) (qW Z Q.1) :=
    Equiv.subtypeEquivRight (fun theta => rawBlock_trivialSector_iff_kernel
      (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
      (OU := OU) (OD := OD) (Q := Q) (CU := CU) (CD := CD)
      (compatU := compatU) (compatD := compatD) (Sglobal := Sglobal) (Slocal := Slocal) theta)
  exact E0.trans (qWDefectZeroEquiv Z hcentral hprimeTo Q.1 Q.2)

theorem trivialSectorRepresentativeEquiv_symm_character_apply
    (eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q))
    (x : NormalizerQuotient Q.1) :
    ((trivialSectorRepresentativeEquiv (iota := iota) (Z := Z)
      (hcentral := hcentral) (hprimeTo := hprimeTo) (OU := OU) (OD := OD) (Q := Q)
      (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
      (Sglobal := Sglobal) (Slocal := Slocal)).symm eta).1.1 x = eta.1 (qW Z Q.1 x) := rfl

variable (sigma : MulAut X) (beta : MulAut (X ⧸ Z))
variable (square : ∀ x : X, QuotientGroup.mk' Z (sigma x) = beta (QuotientGroup.mk' Z x))
variable (stableU : Q.1.comap sigma.toMonoidHom = Q.1)

def trivialSectorRepresentativeFixedEquiv :
    {theta : {theta : LocalDefectZeroCharacter (K := K) Q //
      IsCentralCharacterSector Z (OU.ambientBlockData.blockIdempotent
        (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ)} //
      OrdinaryIrreducibleCharacter.twist K _ theta.1.1 (localAut Q.1 sigma stableU) = theta.1.1} ≃
    {eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q) //
      OrdinaryIrreducibleCharacter.twist K _ eta.1
        (localAut (fixedRadicalImage iota Z hcentral hprimeTo Q).1 beta
          (image_stable (QuotientGroup.mk' Z) sigma beta square Q.1 stableU)) = eta.1} := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  let Qbar := fixedRadicalImage iota Z hcentral hprimeTo Q
  let stableD : Qbar.1.comap beta.toMonoidHom = Qbar.1 :=
    image_stable (QuotientGroup.mk' Z) sigma beta square Q.1 stableU
  let alphaU := localAut Q.1 sigma stableU
  let alphaD := localAut Qbar.1 beta stableD
  let E := trivialSectorRepresentativeEquiv (iota := iota) (Z := Z)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (OU := OU) (OD := OD) (Q := Q)
    (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
    (Sglobal := Sglobal) (Slocal := Slocal)
  have hf : Function.Surjective (qW Z Q.1) :=
    qW_surjective_ofNavarroTiep Z hcentral hprimeTo Q.1 Q.2
      (fixedCentralQuotientSource Z hcentral hprimeTo Q.1 Q.2)
  have hiff (eta : LocalDefectZeroCharacter (K := K) Qbar) :
      OrdinaryIrreducibleCharacter.twist K _ (E.symm eta).1.1 alphaU = (E.symm eta).1.1 ↔
        OrdinaryIrreducibleCharacter.twist K _ eta.1 alphaD = eta.1 :=
    ordinary_fixed_iff_of_factorisation (qW Z Q.1) hf alphaU alphaD
      (qW_localAut_square Z Q.1 sigma beta square stableU) (E.symm eta).1.1 eta.1 (fun x => rfl)
  exact (E.symm.subtypeEquiv (fun eta => (hiff eta).symm)).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
