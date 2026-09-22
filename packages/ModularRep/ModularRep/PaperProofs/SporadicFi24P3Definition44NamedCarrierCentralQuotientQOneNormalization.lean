import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
import ModularRep.BrauerCharacterHomPullback
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! Actual ordinary local bijections for a correspondence in the specified
trivial sector. Their targets retain the support condition at the original radical. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneNormalization

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open CentralEllPrimeIBrFibreTransport CentralEllPrimeWeightLocalQuotient
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

open SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierFixedCentralNormalizerRoot

open EvenFieldFLZ318FixedTheoremGate
open EvenFieldFLZBAWGoodFamily
open CentralEllPrimeIBrFibreTransport
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauer
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels

open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter trivialNormalizerQuotientEquiv)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks

universe u

section Rows
variable {p : ℕ} {K G : Type u} [Field K] [CharZero K] [Group G] [Fintype G]

def atOneLocalRow
    (Q : RadicalSubgroup (p := p) (G := G)) (hQ : Q.val = ⊥)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G)) :
    LocalDefectZeroCharacter (K := K) Q := by
  rcases Q with ⟨Q, hQr⟩
  change Q = ⊥ at hQ
  subst Q
  exact ⟨OrdinaryIrreducibleCharacter.mapEquiv d.val trivialNormalizerQuotientEquiv.symm,
    d.property.mapEquiv trivialNormalizerQuotientEquiv.symm⟩

theorem atOneLocalRow_apply
    (Q : RadicalSubgroup (p := p) (G := G)) (hQ : Q.val = ⊥)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G))
    (n : Subgroup.normalizer (Q.val : Set G)) :
    (atOneLocalRow Q hQ d).val (QuotientGroup.mk n) = d.val n.val := by
  rcases Q with ⟨Q, hQr⟩
  change Q = ⊥ at hQ
  subst Q
  rfl

end Rows

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

local notation "BF" => trivialBrauerFibre iota R Z hcentral

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


variable (eD : IBr (quotientRoot iota Z) ≃ ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
local notation "EU" => transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
local notation "EB" => canonicalBrauerEquiv iota R Z hcentral
local notation "LD" => localQuotientOrdinaryEquiv iota R Z hcentral hprimeTo
  OD CU CD compatU compatD Sglobal Slocal EU

theorem transported_qOne_all_defectZero
    (singleton : DefectZeroReductionBlockSingleton (quotientRoot iota Z) OD)
    (hBlocks : downstairsBlockProperty iota Z OD eD)
    (Q : RadicalSubgroup (p := p) (G := X)) (hQ : Q.val = ⊥) :
    ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X ⧸ Z),
      ∃! phi : brauerAtRadical iota R Z hcentral EU Q,
        IsBrauerReduction (quotientRoot iota Z) d.val ((EB).symm phi.val) ∧
        ∀ n : Subgroup.normalizer ((fixedRadicalImage iota Z hcentral hprimeTo Q).val : Set (X ⧸ Z)),
          (LD Q phi).val (QuotientGroup.mk n) = d.val n.val := by
  intro d
  let Qbar := fixedRadicalImage iota Z hcentral hprimeTo Q
  have hQbar : Qbar.val = ⊥ := by
    change Q.val.map (QuotientGroup.mk' Z) = ⊥
    rw [hQ, Subgroup.map_bot]
  let eta := atOneLocalRow Qbar hQbar d
  let phi := (LD Q).symm eta
  have hLD : LD Q phi = eta := (LD Q).apply_symm_apply eta
  have hvalues (n : Subgroup.normalizer (Qbar.val : Set (X ⧸ Z))) :
      (LD Q phi).val (QuotientGroup.mk n) = d.val n.val :=
    (congrArg (fun theta : LocalDefectZeroCharacter (K := K) Qbar =>
      theta.val (QuotientGroup.mk n)) hLD).trans (atOneLocalRow_apply Qbar hQbar d n)
  let psi := (EB).symm phi.val
  let Wbar := characterWeightAt iota.prime Qbar (LD Q phi)
  have hmatch : rawClass Wbar = eD psi :=
    transported_local_quotient_class iota R Z hcentral hprimeTo
      OD CU CD compatU compatD Sglobal Slocal eD Q phi
  obtain ⟨⟨d', hred', heval'⟩, _hpull⟩ :=
    qOne_localBrauer_of_block_singleton (quotientRoot iota Z) OD compatD
      singleton psi Wbar (CD Qbar (LD Q phi)) hQbar (hBlocks psi Wbar hmatch)
  have hd' : d' = d := by
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    let n : Subgroup.normalizer (Qbar.val : Set (X ⧸ Z)) :=
      ⟨x, by
        rw [hQbar, Subgroup.normalizer_eq_top (⊥ : Subgroup (X ⧸ Z))]
        exact Subgroup.mem_top x⟩
    exact (heval' n).symm.trans (hvalues n)
  have hred : IsBrauerReduction (quotientRoot iota Z) d.val psi := by
    rw [← hd']
    exact hred'
  refine ⟨phi, ⟨hred, hvalues⟩, ?_⟩
  intro phi' hphi'
  apply Subtype.ext
  apply (EB).symm.injective
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro g
  exact (hphi'.1 g).symm.trans (hred g)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneNormalization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
