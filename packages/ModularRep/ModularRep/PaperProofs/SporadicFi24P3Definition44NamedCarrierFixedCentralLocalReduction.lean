import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralNormalizerRoot
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralNormalizer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

/-!
# The local reduction and block image of a factorizing character pair

The two canonical reduction equations and the literal qW square give the
Brauer pullback. Canonical root agreement and uniform local compatibility
then identify the actual normalizer block images.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRawReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierFixedCentralNormalizerRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
open SporadicFi24P3Definition44NamedCarrierCentralNormalizer
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open CentralEllPrimeWeightLocalQuotient

universe u

theorem fixedNormalizer_surjective
    {p : Nat} {X : Type u} [Group X] [Finite X]
    (hp : p.Prime) (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup p Q) :
    Function.Surjective (normalizerMap (QuotientGroup.mk' Z) Q) := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact centralQuotientNormalizerMap_surjective Z hcentral hprimeTo Q hQ
    (fixedCentralQuotientSource Z hcentral hprimeTo Q hQ)

theorem fixedNormalizer_kernel_central
    {X : Type u} [Group X] (Z Q : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) :
    (normalizerMap (QuotientGroup.mk' Z) Q).ker ≤
      Subgroup.center (Subgroup.normalizer (Q : Set X)) := by
  rw [centralNormalizerMap_ker]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hcentral hx) y.1

theorem fixedNormalizer_kernel_primeTo
    {p : Nat} {X : Type u} [Group X] [Finite X]
    (Z Q : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z) :
    ¬ p ∣ Nat.card (normalizerMap (QuotientGroup.mk' Z) Q).ker := by
  have hcard : Nat.card (normalizerMap (QuotientGroup.mk' Z) Q).ker = Nat.card Z := by
    rw [centralNormalizerMap_ker]
    exact Nat.card_congr (localCentralKernelEquiv Z Q hcentral).toEquiv
  rwa [hcard]

variable {p : Nat} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
variable (Q : RadicalSubgroup (p := p) (G := X))
variable (hQbar : IsRadicalSubgroup p (Q.1.map (QuotientGroup.mk' Z)))
variable (theta : LocalDefectZeroCharacter (K := K) Q)
variable (eta : LocalDefectZeroCharacter (K := K)
  (⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ : RadicalSubgroup (p := p) (G := X ⧸ Z)))

theorem localBrauer_pullback
    (CU : CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
    (CD : CanonicalRawReduction (quotientRoot iota Z)
      (characterWeightAt iota.prime ⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ eta))
    (hfactor : theta.1.1 = fun x : NormalizerQuotient Q.1 => eta.1 (qW Z Q.1 x)) :
    CU.localBrauer.1 = PrimeRegularClassFunction.pullback
      (normalizerMap (QuotientGroup.mk' Z) Q.1) CD.localBrauer.1 := by
  let W := characterWeightAt iota.prime Q theta
  let Wbar := characterWeightAt iota.prime
    (⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ : RadicalSubgroup (p := p) (G := X ⧸ Z)) eta
  let fN := normalizerMap (QuotientGroup.mk' Z) Q.1
  let qU := rawNormalizerQuotientMap W
  let qD := rawNormalizerQuotientMap Wbar
  apply PrimeRegularClassFunction.ext
  intro n
  change CU.localBrauer.1 n = CD.localBrauer.1 (PrimeRegularElement.map fN n)
  have hsquare : qD (fN n.1) = qW Z Q.1 (qU n.1) :=
    DFunLike.congr_fun (qW_quotient_square Z Q.1) n.1
  calc
    CU.localBrauer.1 n = theta.1 (qU n.1) := (CU.localBrauer_reduction n).symm
    _ = eta.1 (qW Z Q.1 (qU n.1)) := congrFun hfactor (qU n.1)
    _ = eta.1 (qD (fN n.1)) := congrArg eta.1 hsquare.symm
    _ = CD.localBrauer.1 (PrimeRegularElement.map fN n) :=
      CD.localBrauer_reduction (PrimeRegularElement.map fN n)

theorem localPhysicalBlock_image
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
    (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
      (normalizerMap (QuotientGroup.mk' Z) Q.1)
      (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
      (fixedNormalizer_kernel_central Z Q.1 hcentral)
      (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo)) :
    algebraMapOf (normalizerMap (QuotientGroup.mk' Z) Q.1)
      (OU.inflateToNormalizer Q.1 (OU.localCharacterBlock Q.1 theta.1 theta.2)).1 =
      (OD.inflateToNormalizer (Q.1.map (QuotientGroup.mk' Z))
        (OD.localCharacterBlock (Q.1.map (QuotientGroup.mk' Z)) eta.1 eta.2)).1 := by
  let W := characterWeightAt iota.prime Q theta
  let Wbar := characterWeightAt iota.prime
    (⟨Q.1.map (QuotientGroup.mk' Z), hQbar⟩ : RadicalSubgroup (p := p) (G := X ⧸ Z)) eta
  let fN := normalizerMap (QuotientGroup.mk' Z) Q.1
  let hfN := fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2
  let DU := OU.inflatedNormalizerBlockData Q.1
  let DD := OD.inflatedNormalizerBlockData (Q.1.map (QuotientGroup.mk' Z))
  let := DU.fintypeBlock
  let := DD.fintypeBlock
  let injU := irreducibleBrauerCharacterInjectivity_of_rootEmbedding CU.normalizerRoot
  let injD := irreducibleBrauerCharacterInjectivity_of_rootEmbedding CD.normalizerRoot
  have hU : irreducibleBrauerCharacterBlock CU.normalizerRoot injU DU.blocks CU.localBrauer =
      OU.inflateToNormalizer Q.1 (OU.localCharacterBlock Q.1 theta.1 theta.2) :=
    compatU.normalizerBrauerBlock_eq_inflateToNormalizer W CU
  have hD : irreducibleBrauerCharacterBlock CD.normalizerRoot injD DD.blocks CD.localBrauer =
      OD.inflateToNormalizer (Q.1.map (QuotientGroup.mk' Z))
        (OD.localCharacterBlock (Q.1.map (QuotientGroup.mk' Z)) eta.1 eta.2) :=
    compatD.normalizerBrauerBlock_eq_inflateToNormalizer Wbar CD
  have hphysical := actualBrauerBlock_image fN hfN iota.prime
    (fixedNormalizer_kernel_central Z Q.1 hcentral)
    (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo)
    Slocal CU.normalizerRoot CD.normalizerRoot
    (fun V => fixedZ_sourceNormalizerRoot_compatible iota Z W Wbar CU CD fN hfN V.ρ)
    injU injD DU.blocks DD.blocks CU.localBrauer CD.localBrauer
    (localBrauer_pullback iota Z Q hQbar theta eta CU CD hfactor)
  have hUval := congrArg Subtype.val hU
  have hDval := congrArg Subtype.val hD
  calc
    _ = algebraMapOf fN
        (irreducibleBrauerCharacterBlock CU.normalizerRoot injU DU.blocks CU.localBrauer).1 :=
      congrArg (algebraMapOf fN) hUval.symm
    _ = (irreducibleBrauerCharacterBlock CD.normalizerRoot injD DD.blocks CD.localBrauer).1 :=
      hphysical
    _ = _ := hDval

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
