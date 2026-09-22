import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInducedBlockImage

/-!
# The ambient block image of a factorizing local character pair

The local image comes from the same two canonical reductions. Both actual
operations give their own induction facts; normalizer saturation supplies
the coefficient-restriction square. No ambient block image is assumed.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralWeightBlockImage

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierInducedBlockImage
open CentralEllPrimeWeightLocalQuotient

universe u

variable {p : Nat} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) :=
  Fintype.ofFinite _
local instance subgroupFintype {Y : Type u} [Group Y] [Finite Y] (H : Subgroup Y) :
    Fintype H := Fintype.ofFinite H

variable (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
variable (Q : RadicalSubgroup (p := p) (G := X))
variable (hQbar : IsRadicalSubgroup p (Q.1.map (QuotientGroup.mk' Z)))
variable (theta : LocalDefectZeroCharacter (K := K) Q)
variable (eta : LocalDefectZeroCharacter (K := K)
  (⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ : RadicalSubgroup (p := p) (G := X ⧸ Z)))

theorem rawWeightBlock_image
    (CU : CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
    (CD : CanonicalRawReduction (quotientRoot iota Z)
      (characterWeightAt iota.prime ⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ eta))
    (hfactor : theta.1.1 = fun x : NormalizerQuotient Q.1 => eta.1 (qW Z Q.1 x))
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    {BlockU BlockD : Type u}
    [MulAction (MulAut X)ᵐᵒᵖ BlockU] [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
    (OU : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := X) (Block := BlockU))
    (OD : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
    (compatU : CanonicalLocalBlockCompatibility iota OU)
    (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
    (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
      (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
      (by simpa only [QuotientGroup.ker_mk'] using hcentral)
      (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
    (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
      (normalizerMap (QuotientGroup.mk' Z) Q.1)
      (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
      (fixedNormalizer_kernel_central Z Q.1 hcentral)
      (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo)) :
    algebraMapOf (QuotientGroup.mk' Z)
      (OU.ambientBlockData.blockIdempotent
        (OU.rawWeightBlock (characterWeightAt iota.prime Q theta))) =
      OD.ambientBlockData.blockIdempotent
        (OD.rawWeightBlock (characterWeightAt iota.prime
          ⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ eta)) := by
  let W := characterWeightAt iota.prime Q theta
  let Wbar := characterWeightAt iota.prime
    (⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ : RadicalSubgroup (p := p) (G := X ⧸ Z)) eta
  let pi := QuotientGroup.mk' Z
  let N := Subgroup.normalizer (Q.1 : Set X)
  let Nbar := Subgroup.normalizer (Q.1.map pi : Set (X ⧸ Z))
  let fN := normalizerMap pi Q.1
  let hfN := fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2
  let DU := OU.inflatedNormalizerBlockData Q.1
  let DD := OD.inflatedNormalizerBlockData (Q.1.map pi)
  let := OU.ambientBlockData.fintypeBlock
  let := OD.ambientBlockData.fintypeBlock
  let := DU.fintypeBlock
  let := DD.fintypeBlock
  let bU := OU.inflateToNormalizer Q.1 (OU.localCharacterBlock Q.1 theta.1 theta.2)
  let bD := OD.inflateToNormalizer (Q.1.map pi)
    (OD.localCharacterBlock (Q.1.map pi) eta.1 eta.2)
  have hc : pi.ker ≤ Subgroup.center X := by
    simpa only [pi, QuotientGroup.ker_mk'] using hcentral
  have hk : ¬ p ∣ Nat.card pi.ker := by
    simpa only [pi, QuotientGroup.ker_mk'] using hprimeTo
  have hcomap : Nbar.comap pi = N :=
    normalizer_comap_of_central_primeTo iota.prime pi hc hk Q.1 Q.2.isPGroup
  have hsaturated : ∀ x : X, x ∈ N ↔ pi x ∈ Nbar := by
    intro x
    change x ∈ N ↔ x ∈ Nbar.comap pi
    rw [hcomap]
  have hlocal : algebraMapOf fN bU.1 = bD.1 :=
    localPhysicalBlock_image iota Z Q hQbar theta eta CU CD hfactor
      hcentral hprimeTo OU OD compatU compatD Slocal
  have hup : BlockInducesTo N DU.catalogue OU.ambientBlockData.catalogue bU
      (OU.rawWeightBlock W) :=
    inducedBlock_spec N DU.catalogue OU.ambientBlockData.catalogue bU (OU.blockInductionDefined W)
  have hdown : BlockInducesTo Nbar DD.catalogue OD.ambientBlockData.catalogue bD
      (OD.rawWeightBlock Wbar) :=
    inducedBlock_spec Nbar DD.catalogue OD.ambientBlockData.catalogue bD (OD.blockInductionDefined Wbar)
  exact blockInducesTo_image_of_local_image N Nbar
    pi (QuotientGroup.mk'_surjective Z) fN hfN (fun _ => rfl) hsaturated
    OU.ambientBlockData.catalogue OD.ambientBlockData.catalogue DU.catalogue DD.catalogue
    bU bD (OU.rawWeightBlock W) (OD.rawWeightBlock Wbar)
    Sglobal.primitive_image_of_ne_zero hlocal hup hdown

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralWeightBlockImage


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
