import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientPhysicalWeights
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction

/-! Central prime-to-p quotient transport on the specified trivial sector.
The constructed equivalence has the literal raw character and subgroup formula,
preserves the specified induced block, and commutes with every quotient square. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

open ModularRep ModularRep.CharacterWeight
open CentralEllPrimeWeightLocalQuotient
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientPhysicalWeights
open SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightWitnesses
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel

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


local notation "E" => sectorToQuotient iota R Z hcentral hprimeTo
  OD CU CD compatU compatD Sglobal Slocal

include CU compatU hcentral hprimeTo in
theorem sectorRawKernel (w : SectorWeights R Z) (W : CharacterWeight p K X)
    (hclass : rawClass W = w.val) : KernelConstant Z W :=
  raw_kernel_of_sector iota R Z hcentral hprimeTo w W hclass
    (CU ⟨W.subgroup, W.radical⟩ ⟨W.localCharacter, W.defectZero⟩) compatU

local notation "HK" => sectorRawKernel iota R Z hcentral hprimeTo CU compatU

theorem sectorToQuotient_apply_raw (w : SectorWeights R Z) (W : CharacterWeight p K X)
    (hclass : rawClass W = w.val) :
    E w = rawClass (rawDescent Z hcentral hprimeTo W (HK w W hclass)) := by
  obtain ⟨Q, theta, eta, hUp, hDown, factor⟩ :=
    sectorToQuotient_factorising_witness iota R Z hcentral hprimeTo
      OD CU CD compatU compatD Sglobal Slocal w
  let W0 := characterWeightAt iota.prime Q theta
  let U0 := characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta
  have hk0 : KernelConstant Z W0 :=
    kernelConstant_of_factorisation Z W0 eta.val factor
  have hU0 : U0 = rawDescent Z hcentral hprimeTo W0 hk0 :=
    rawDescent_unique Z hcentral hprimeTo W0 hk0 U0 rfl factor
  change rawClass W0 = w.val at hUp
  change rawClass U0 = E w at hDown
  exact hDown.symm.trans ((congrArg rawClass hU0).trans
    (rawDescent_class_congr Z hcentral hprimeTo W0 W hk0 (HK w W hclass)
      (hUp.trans hclass.symm)))

theorem sectorToQuotient_covariance (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (w : SectorWeights R Z) :
    E (sectorTwist R Z hcentral alpha beta square w) = MulOpposite.op beta • E w := by
  obtain ⟨W, hW⟩ := rawClass_surjective (p := p) (K := K) (X := X) w.val
  have hTw : rawClass (W.rightTwist alpha) =
      (sectorTwist R Z hcentral alpha beta square w).val := by
    rw [rawClass_rightTwist, hW, sectorTwist_val]
  rw [sectorToQuotient_apply_raw iota R Z hcentral hprimeTo OD CU CD
    compatU compatD Sglobal Slocal _ (W.rightTwist alpha) hTw,
    sectorToQuotient_apply_raw iota R Z hcentral hprimeTo OD CU CD
      compatU compatD Sglobal Slocal w W hW]
  exact (congrArg rawClass
    (rawDescent_rightTwist Z hcentral hprimeTo W (HK w W hW) alpha beta square)).trans
      (rawClass_rightTwist (rawDescent Z hcentral hprimeTo W (HK w W hW)) beta)

theorem central_quotient_weight_transport_with_invertible :
    (∀ (w : SectorWeights R Z) (W : CharacterWeight p K X), rawClass W = w.val →
      ∃ Wbar : CharacterWeight p K (X ⧸ Z),
        rawClass Wbar = E w ∧
        Wbar.subgroup = W.subgroup.map (QuotientGroup.mk' Z) ∧
        (∃ hQ : Wbar.subgroup = W.subgroup.map (QuotientGroup.mk' Z),
          ∀ x : NormalizerQuotient W.subgroup,
            castLocalCharacter hQ Wbar.localCharacter (qW Z W.subgroup x) = W.localCharacter x) ∧
        algebraMapOf (QuotientGroup.mk' Z) (R.1.weightBlock w.val).val =
          OD.ambientBlockData.blockIdempotent (OD.rawWeightBlock Wbar)) ∧
    (∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
      (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
      (w : SectorWeights R Z),
      E (sectorTwist R Z hcentral alpha beta square w) = MulOpposite.op beta • E w) := by
  constructor
  · intro w W hW
    let hk := HK w W hW
    let Wbar := rawDescent Z hcentral hprimeTo W hk
    refine ⟨Wbar, (sectorToQuotient_apply_raw iota R Z hcentral hprimeTo OD CU CD
      compatU compatD Sglobal Slocal w W hW).symm, rfl, ⟨rfl, ?_⟩, ?_⟩
    · exact rawDescent_character Z hcentral hprimeTo W hk
    · have himage := rawDescent_block_image iota Z hcentral hprimeTo R.1.operations OD W hk
        (CU ⟨W.subgroup, W.radical⟩ ⟨W.localCharacter, W.defectZero⟩)
        (CD ⟨Wbar.subgroup, Wbar.radical⟩ ⟨Wbar.localCharacter, Wbar.defectZero⟩)
        compatU compatD Sglobal (Slocal ⟨W.subgroup, W.radical⟩)
      rw [R.2] at himage
      change algebraMapOf (QuotientGroup.mk' Z) (R.1.weightBlock (rawClass W)).val = _ at himage
      rw [hW] at himage
      exact himage
  · exact sectorToQuotient_covariance iota R Z hcentral hprimeTo OD CU CD
      compatU compatD Sglobal Slocal

omit [Invertible (Fintype.card Z : k)] in
theorem central_quotient_weight_transport_deduction :
    let _ := fixedCentralCardInvertible (k := k) Z hprimeTo
    (∀ (w : SectorWeights R Z) (W : CharacterWeight p K X), rawClass W = w.val →
      ∃ Wbar : CharacterWeight p K (X ⧸ Z),
        rawClass Wbar = E w ∧
        Wbar.subgroup = W.subgroup.map (QuotientGroup.mk' Z) ∧
        (∃ hQ : Wbar.subgroup = W.subgroup.map (QuotientGroup.mk' Z),
          ∀ x : NormalizerQuotient W.subgroup,
            castLocalCharacter hQ Wbar.localCharacter (qW Z W.subgroup x) = W.localCharacter x) ∧
        algebraMapOf (QuotientGroup.mk' Z) (R.1.weightBlock w.val).val =
          OD.ambientBlockData.blockIdempotent (OD.rawWeightBlock Wbar)) ∧
    (∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
      (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
      (w : SectorWeights R Z),
      E (sectorTwist R Z hcentral alpha beta square w) = MulOpposite.op beta • E w) := by
  let _ := fixedCentralCardInvertible (k := k) Z hprimeTo
  exact central_quotient_weight_transport_with_invertible iota R Z hcentral hprimeTo
    OD CU CD compatU compatD Sglobal Slocal

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
