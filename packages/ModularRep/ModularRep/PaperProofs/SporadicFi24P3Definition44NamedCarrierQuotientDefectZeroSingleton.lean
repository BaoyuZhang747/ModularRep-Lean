import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryInflation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel

/-! Original defect-zero block uniqueness supplies the same uniform quotient
uniqueness. No correspondence, local reduction or quotient singleton is an input. -/
noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientDefectZeroSingleton

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open CentralEllPrimeIBrFibreTransport
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryInflation
open SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource defectZeroBrauerFibre_subsingleton)

universe u
variable {p : ℕ} {k K G BlockD : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]

local instance subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite _
local instance quotientFintype (Z : Subgroup G) [Z.Normal] :
    Fintype (G ⧸ Z) := Fintype.ofFinite _

theorem quotient_defectZeroReductionBlockSingleton
    (iota : PrimeRegularRootEmbedding p k K G)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G)
    (hprimeTo : ¬ p ∣ Nat.card Z)
    [MulAction (MulAut (G ⧸ Z))ᵐᵒᵖ BlockD]
    (OD : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G ⧸ Z) (Block := BlockD))
    (Dzero : DefectZeroReductionSource iota)
    (Bzero : letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks Dzero)
    (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
      (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
      (by simpa only [QuotientGroup.ker_mk'] using hcentral)
      (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)) :
    DefectZeroReductionBlockSingleton (quotientRoot iota Z) OD := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  let _ := OD.ambientBlockData.fintypeBlock
  let _ := fixedCentralCardInvertible (k := k) Z hprimeTo
  let inj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let j := quotientRoot iota Z
  let injD := irreducibleBrauerCharacterInjectivity_of_rootEmbedding j
  let E := quotientIBrEquivTrivialCentralCharacterFibre
    iota j (canonicalQuotientRealisation iota Z)
    R.1.operations.ambientBlockData.blocks inj hcentral
  dsimp only [DefectZeroReductionBlockSingleton]
  intro d chi hred
  let pi := QuotientGroup.mk' Z
  have hpi : Function.Surjective pi := QuotientGroup.mk'_surjective Z
  have hker : ¬ p ∣ Nat.card pi.ker := by
    simpa only [pi, QuotientGroup.ker_mk'] using hprimeTo
  let dU : GlobalDefectZeroCharacter (p := p) (K := K) (X := G) :=
    ⟨OrdinaryIrreducibleCharacter.inflateAlong pi hpi d.val,
      inflateAlong_defectZero pi hpi hker d.val d.property⟩
  have hreduce : Dzero.reduce (iota := iota) dU = (E chi).val := by
    apply Subtype.ext
    ext g
    change (Dzero.reduce (iota := iota) dU).val g =
      chi.val (PrimeRegularElement.map pi g)
    exact (Dzero.reduce_isReduction (iota := iota) dU g).symm.trans
      (hred (PrimeRegularElement.map pi g))
  have hUp : Subsingleton {psi : IBr iota //
      irreducibleBrauerCharacterBlock iota inj
          R.1.operations.ambientBlockData.blocks psi =
        irreducibleBrauerCharacterBlock iota inj
          R.1.operations.ambientBlockData.blocks (E chi).val} := by
    change Subsingleton {psi : IBr iota //
      operationsBlock iota inj R psi = operationsBlock iota inj R (E chi).val}
    simpa only [
      operationsBlock_eq iota inj R R.1.operations.ambientBlockData.blocks,
      hreduce] using
      (defectZeroBrauerFibre_subsingleton
        (iota := iota) (hinj := inj)
        (blocks := R.1.operations.ambientBlockData.blocks) Dzero Bzero dU)
  let _ := hUp
  let F := physicalBrauerBlockFibreEquiv iota Z
    R.1.operations.ambientBlockData.blocks OD.ambientBlockData.blocks
    inj injD hcentral hprimeTo Sglobal (E chi)
  have hDown : Subsingleton {psi : IBr j //
      irreducibleBrauerCharacterBlock j injD OD.ambientBlockData.blocks psi =
        irreducibleBrauerCharacterBlock j injD OD.ambientBlockData.blocks
          (E.symm (E chi))} := F.symm.subsingleton
  simpa only [Equiv.symm_apply_apply] using hDown

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientDefectZeroSingleton


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
