import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction

/-!
# Fixed representative and weight fibres through the same central quotient

The inverse character is literal inflation. The local action square and
factorization are derived internally before restricting the accepted map.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFixedPoints

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
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
variable (RU : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := X) (Block := BlockU))
variable (RD : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Q : RadicalSubgroup (p := p) (G := X))
variable (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q),
  CanonicalRawReduction (quotientRoot iota Z)
    (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota RU.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) RD.operations)
variable (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' Z) Q.1)
  (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
  (fixedNormalizer_kernel_central Z Q.1 hcentral)
  (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))

theorem representativeDZEquiv_symm_character_apply (b : BlockU)
    (hb : IsCentralCharacterSector Z (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ))
    (eta : RepresentativeDZ iota.prime RD (fixedRadicalImage iota Z hcentral hprimeTo Q)
      (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb))
    (x : NormalizerQuotient Q.1) :
    ((representativeDZEquiv (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
      (RU := RU) (RD := RD) (Sglobal := Sglobal) (Q := Q) (CU := CU) (CD := CD)
      (compatU := compatU) (compatD := compatD) (Slocal := Slocal) b hb).symm eta).1.1 x =
        eta.1.1 (qW Z Q.1 x) := rfl

variable (sigma : MulAut X) (beta : MulAut (X ⧸ Z))
variable (square : ∀ x : X, QuotientGroup.mk' Z (sigma x) = beta (QuotientGroup.mk' Z x))
variable (stableU : Q.1.comap sigma.toMonoidHom = Q.1)

def representativeDZFixedEquiv (b : BlockU)
    (hb : IsCentralCharacterSector Z (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    {theta : RepresentativeDZ iota.prime RU Q b //
      OrdinaryIrreducibleCharacter.twist K _ theta.1.1 (localAut Q.1 sigma stableU) = theta.1.1} ≃
    {eta : RepresentativeDZ iota.prime RD (fixedRadicalImage iota Z hcentral hprimeTo Q)
        (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb) //
      OrdinaryIrreducibleCharacter.twist K _ eta.1.1
        (localAut (fixedRadicalImage iota Z hcentral hprimeTo Q).1 beta
          (image_stable (QuotientGroup.mk' Z) sigma beta square Q.1 stableU)) = eta.1.1} := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  let Qbar := fixedRadicalImage iota Z hcentral hprimeTo Q
  let bD := quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb
  let stableD : Qbar.1.comap beta.toMonoidHom = Qbar.1 :=
    image_stable (QuotientGroup.mk' Z) sigma beta square Q.1 stableU
  let alphaU := localAut Q.1 sigma stableU
  let alphaD := localAut Qbar.1 beta stableD
  let E := representativeDZEquiv (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
    (RU := RU) (RD := RD) (Sglobal := Sglobal) (Q := Q) (CU := CU) (CD := CD)
    (compatU := compatU) (compatD := compatD) (Slocal := Slocal) b hb
  have hf : Function.Surjective (qW Z Q.1) :=
    qW_surjective_ofNavarroTiep Z hcentral hprimeTo Q.1 Q.2
      (fixedCentralQuotientSource Z hcentral hprimeTo Q.1 Q.2)
  have hiff (eta : RepresentativeDZ iota.prime RD Qbar bD) :
      OrdinaryIrreducibleCharacter.twist K _ (E.symm eta).1.1 alphaU = (E.symm eta).1.1 ↔
        OrdinaryIrreducibleCharacter.twist K _ eta.1.1 alphaD = eta.1.1 :=
    ordinary_fixed_iff_of_factorisation (qW Z Q.1) hf alphaU alphaD
      (qW_localAut_square Z Q.1 sigma beta square stableU) (E.symm eta).1.1 eta.1.1 (fun x => rfl)
  exact (E.symm.subtypeEquiv (fun eta => (hiff eta).symm)).symm

def weightBlockRadicalFixedEquiv (b : BlockU)
    (hb : IsCentralCharacterSector Z (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    {w : WeightBlockRadicalFibre RU Q b // MulOpposite.op sigma • w.1 = w.1} ≃
    {w : WeightBlockRadicalFibre RD (fixedRadicalImage iota Z hcentral hprimeTo Q)
        (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb) //
      MulOpposite.op beta • w.1 = w.1} := by
  let E := representativeDZFixedEquiv (iota := iota) (Z := Z)
    (hcentral := hcentral) (hprimeTo := hprimeTo) (RU := RU) (RD := RD)
    (Sglobal := Sglobal) (Q := Q) (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
    (Slocal := Slocal) (sigma := sigma) (beta := beta) (square := square) (stableU := stableU) b hb
  exact (fixedRepresentativeDZEquiv iota.prime RU Q b sigma stableU).symm.trans
    (E.trans (fixedRepresentativeDZEquiv iota.prime RD
      (fixedRadicalImage iota Z hcentral hprimeTo Q)
      (quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb) beta
      (image_stable (QuotientGroup.mk' Z) sigma beta square Q.1 stableU)))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFixedPoints


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
