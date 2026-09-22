import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses

/-! Specified support supplies the raw character kernel condition. The same
canonical reductions identify the induced block of the actual descended weight. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientPhysicalWeights

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralCharacterKernel
open SporadicFi24P3Definition44NamedCarrierFixedCentralWeightBlockImage
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

theorem raw_kernel_of_sector
    (iota : PrimeRegularRootEmbedding p k K X)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    (w : SectorWeights R Z) (W : CharacterWeight p K X)
    (hclass : rawClass W = w.val)
    (CU : CanonicalRawReduction iota W)
    (compatU : CanonicalLocalBlockCompatibility iota R.1.operations) :
    KernelConstant Z W := by
  have hblock : R.1.operations.rawWeightBlock W = R.1.weightBlock w.val :=
    congrArg R.1.weightBlock hclass
  apply fixedZ_character_constant_on_qW_kernel
    iota R.1.operations W CU compatU Z hcentral hprimeTo
  rw [R.2, hblock]
  exact w.property.mul_eq_self

theorem rawDescent_block_image
    (iota : PrimeRegularRootEmbedding p k K X)
    (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    {BlockU BlockD : Type u}
    [MulAction (MulAut X)ᵐᵒᵖ BlockU] [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
    (OU : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := X) (Block := BlockU))
    (OD : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
    (W : CharacterWeight p K X) (hkernel : KernelConstant Z W)
    (CU : CanonicalRawReduction iota W)
    (CD : CanonicalRawReduction (quotientRoot iota Z)
      (rawDescent Z hcentral hprimeTo W hkernel))
    (compatU : CanonicalLocalBlockCompatibility iota OU)
    (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
    (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
      (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
      (by simpa only [QuotientGroup.ker_mk'] using hcentral)
      (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
    (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
      (normalizerMap (QuotientGroup.mk' Z) W.subgroup)
      (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo W.subgroup W.radical)
      iota.prime
      (fixedNormalizer_kernel_central Z W.subgroup hcentral)
      (fixedNormalizer_kernel_primeTo Z W.subgroup hcentral hprimeTo)) :
    algebraMapOf (QuotientGroup.mk' Z)
      (OU.ambientBlockData.blockIdempotent (OU.rawWeightBlock W)) =
      OD.ambientBlockData.blockIdempotent (OD.rawWeightBlock
        (rawDescent Z hcentral hprimeTo W hkernel)) := by
  let Wbar := rawDescent Z hcentral hprimeTo W hkernel
  let Q : RadicalSubgroup (p := p) (G := X) := ⟨W.subgroup, W.radical⟩
  let Qbar : RadicalSubgroup (p := p) (G := X ⧸ Z) :=
    ⟨Q.val.map (QuotientGroup.mk' Z), Wbar.radical⟩
  let theta : LocalDefectZeroCharacter (K := K) Q :=
    ⟨W.localCharacter, W.defectZero⟩
  let eta : LocalDefectZeroCharacter (K := K) Qbar :=
    ⟨Wbar.localCharacter, Wbar.defectZero⟩
  have hW : characterWeightAt iota.prime Q theta = W := rfl
  have hWbar : characterWeightAt iota.prime Qbar eta = Wbar := rfl
  have hfactor : theta.val.val = fun x : NormalizerQuotient Q.val =>
      eta.val (CentralEllPrimeWeightLocalQuotient.qW Z Q.val x) := by
    funext x
    exact (rawDescent_character Z hcentral hprimeTo W hkernel x).symm
  exact rawWeightBlock_image iota Z Q Qbar.property theta eta
    (by rw [hW]; exact CU) (by rw [hWbar]; exact CD)
    hfactor hcentral hprimeTo OU OD compatU compatD Sglobal Slocal

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientPhysicalWeights


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
