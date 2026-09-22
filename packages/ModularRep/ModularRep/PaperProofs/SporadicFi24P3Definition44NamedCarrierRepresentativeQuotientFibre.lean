import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToLocalOrdinaryEquiv
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralCharacterKernel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralWeightBlockImage
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockMap

/-!
# Representative block/radical fibres under a central prime-to-p quotient

The radical image and quotient block are computed from the literal map.
Kernel constancy and both block-membership directions are derived before
restricting ordinary inflation and descent to the representative rows.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre

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
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockMap
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open CentralEllPrimeWeightLocalQuotient

universe u

variable {p : Nat} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) :=
  Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H

variable (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

def fixedRadicalImage (Q : RadicalSubgroup (p := p) (G := X)) :
    RadicalSubgroup (p := p) (G := X ⧸ Z) := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  exact ⟨Q.1.map (QuotientGroup.mk' Z),
    (fixedCentralQuotientSource Z hcentral hprimeTo Q.1 Q.2).radical_image⟩

omit [CharP k p] [IsAlgClosed k] [CharZero K] in
@[simp]
theorem fixedRadicalImage_val (Q : RadicalSubgroup (p := p) (G := X)) :
    (fixedRadicalImage iota Z hcentral hprimeTo Q).1 = Q.1.map (QuotientGroup.mk' Z) := rfl

variable [Invertible (Fintype.card Z : k)]
variable {BlockU BlockD : Type u}
variable [MulAction (MulAut X)ᵐᵒᵖ BlockU] [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (RU : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := X) (Block := BlockU))
variable (RD : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))

def quotientBlock (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) : BlockD := by
  let := RU.operations.ambientBlockData.fintypeBlock
  let := RD.operations.ambientBlockData.fintypeBlock
  exact quotientBlockIndex Z iota.prime hcentral hprimeTo Sglobal
    RD.operations.ambientBlockData.blocks
    ⟨RU.operations.ambientBlockData.blockIdempotent b,
      RU.operations.ambientBlockData.blocks.primitive b⟩ hb

theorem quotientBlock_value (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    RD.operations.ambientBlockData.blockIdempotent
        (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb) =
      algebraMapOf (QuotientGroup.mk' Z) (RU.operations.ambientBlockData.blockIdempotent b) := by
  let := RU.operations.ambientBlockData.fintypeBlock
  let := RD.operations.ambientBlockData.fintypeBlock
  exact quotientBlockIndex_value Z iota.prime hcentral hprimeTo Sglobal
    RD.operations.ambientBlockData.blocks
    ⟨RU.operations.ambientBlockData.blockIdempotent b,
      RU.operations.ambientBlockData.blocks.primitive b⟩ hb

variable (Q : RadicalSubgroup (p := p) (G := X))
variable (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ eta : LocalDefectZeroCharacter (K := K)
    (fixedRadicalImage iota Z hcentral hprimeTo Q),
  CanonicalRawReduction (quotientRoot iota Z)
    (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota RU.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) RD.operations)
variable (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' Z) Q.1)
  (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
  (fixedNormalizer_kernel_central Z Q.1 hcentral)
  (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))

def representativeDZEquiv (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    RepresentativeDZ iota.prime RU Q b ≃
      RepresentativeDZ iota.prime RD (fixedRadicalImage iota Z hcentral hprimeTo Q)
        (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb) := by
  classical
  let _ : Fact p.Prime := ⟨iota.prime⟩
  let OU := RU.operations
  let OD := RD.operations
  let DU := OU.ambientBlockData
  let DD := OD.ambientBlockData
  let := DU.fintypeBlock
  let := DD.fintypeBlock
  let Qbar := fixedRadicalImage iota Z hcentral hprimeTo Q
  let eU := DU.blockIdempotent
  let eD := DD.blockIdempotent
  let F := algebraMapOf (k := k) (QuotientGroup.mk' Z)
  let BU := fun theta : LocalDefectZeroCharacter (K := K) Q =>
    OU.rawWeightBlock (characterWeightAt iota.prime Q theta)
  let BD := fun eta : LocalDefectZeroCharacter (K := K) Qbar =>
    OD.rawWeightBlock (characterWeightAt iota.prime Qbar eta)
  let bD := quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb
  let D := KernelConstantDefectZeroIrr (p := p) (K := K) (qW Z Q.1)
  let E : D ≃ LocalDefectZeroCharacter (K := K) Qbar :=
    qWDefectZeroEquiv Z hcentral hprimeTo Q.1 Q.2
  change {theta : LocalDefectZeroCharacter (K := K) Q // BU theta = b} ≃
    {eta : LocalDefectZeroCharacter (K := K) Qbar // BD eta = bD}
  have hbD : eD bD = F (eU b) :=
    quotientBlock_value iota Z hcentral hprimeTo RU RD Sglobal b hb
  have factor (t : D) : t.1.1.1 = fun x : NormalizerQuotient Q.1 => (E t).1 (qW Z Q.1 x) :=
    descendCharacter_factorisation (qW Z Q.1)
      (qW_surjective_ofNavarroTiep Z hcentral hprimeTo Q.1 Q.2
        (fixedCentralQuotientSource Z hcentral hprimeTo Q.1 Q.2)) t.1.1 t.2
  have image (t : D) : F (eU (BU t.1)) = eD (BD (E t)) :=
    rawWeightBlock_image iota Z Q Qbar.2 t.1 (E t) (CU t.1) (CD (E t)) (factor t)
      hcentral hprimeTo OU OD compatU compatD Sglobal Slocal
  have hiff (t : D) : BU t.1 = b ↔ BD (E t) = bD := by
    constructor
    · intro ht
      apply DD.blocks.primitiveBlockOfIndex_injective
      apply Subtype.ext
      exact (image t).symm.trans ((congrArg (fun c => F (eU c)) ht).trans hbD.symm)
    · intro ht
      apply blockIndex_eq_of_map_eq_of_ne_zero DU.blocks F.toRingHom (BU t.1) b
      · exact (image t).trans ((congrArg eD ht).trans hbD)
      · change F (eU (BU t.1)) ≠ 0
        rw [image t]
        exact (DD.blocks.primitive (BD (E t))).ne_zero
  have rowKernel {theta : LocalDefectZeroCharacter (K := K) Q} (ht : BU theta = b) :
      ∀ x : (qW Z Q.1).ker, theta.1 (x : NormalizerQuotient Q.1) = theta.1 1 := by
    exact fixedZ_character_constant_on_qW_kernel iota OU
      (characterWeightAt iota.prime Q theta) (CU theta) compatU Z hcentral hprimeTo (by
        change eU (BU theta) * centralCharacterIdempotent Z (1 : Z →* kˣ) = eU (BU theta)
        rw [ht]
        exact hb.mul_eq_self)
  let flatten : {t : D // BU t.1 = b} ≃
      {theta : LocalDefectZeroCharacter (K := K) Q // BU theta = b} :=
    Equiv.subtypeSubtypeEquivSubtype rowKernel
  let restricted : {t : D // BU t.1 = b} ≃
      {eta : LocalDefectZeroCharacter (K := K) Qbar // BD eta = bD} := E.subtypeEquiv hiff
  exact flatten.symm.trans restricted

def weightBlockRadicalFibreEquiv (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    WeightBlockRadicalFibre RU Q b ≃
      WeightBlockRadicalFibre RD (fixedRadicalImage iota Z hcentral hprimeTo Q)
        (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb) := by
  let E := representativeDZEquiv (iota := iota) (Z := Z)
    (hcentral := hcentral) (hprimeTo := hprimeTo)
    (RU := RU) (RD := RD) (Sglobal := Sglobal) (Q := Q)
    (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD) (Slocal := Slocal) b hb
  exact (representativeDZEquivWeightBlockRadicalFibre iota.prime RU Q b).symm.trans
    (E.trans (representativeDZEquivWeightBlockRadicalFibre iota.prime RD
      (fixedRadicalImage iota Z hcentral hprimeTo Q)
      (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb)))

include CU CD compatU compatD Sglobal Slocal in
theorem weightBlockRadicalFibre_card (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    Nat.card (WeightBlockRadicalFibre RU Q b) =
      Nat.card (WeightBlockRadicalFibre RD (fixedRadicalImage iota Z hcentral hprimeTo Q)
        (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb)) :=
  Nat.card_congr (weightBlockRadicalFibreEquiv (iota := iota) (Z := Z)
    (hcentral := hcentral) (hprimeTo := hprimeTo)
    (RU := RU) (RD := RD) (Sglobal := Sglobal) (Q := Q)
    (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD) (Slocal := Slocal) b hb)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
