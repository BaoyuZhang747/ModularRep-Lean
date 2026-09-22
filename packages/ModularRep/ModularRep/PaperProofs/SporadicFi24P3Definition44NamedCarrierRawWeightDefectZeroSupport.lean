import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizerDefectZeroSupport

/-! Standard local defect inputs on the actual inflated normalizer blocks.
The record below lists three independent E1 foundations, without any
weight conclusion. The selected ambient trivial-defect fact is separate. -/

noncomputable section
open ModularRep ModularRep.CharacterWeight
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierNormalizerDefectZeroSupport

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fact p.Prime]

structure RadicalNormalizerDefectSources
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G)) : Prop where
  localExistence : ∀ Q : CharacterWeight.RadicalSubgroup (p := p) (G := G),
    let data := R.1.operations.inflatedNormalizerBlockData Q.1
    letI := data.fintypeBlock
    Navarro417LocalDefectExistenceSource (p := p) Q.1 data.blocks
  pCoreContainment : ∀ Q : CharacterWeight.RadicalSubgroup (p := p) (G := G),
    let data := R.1.operations.inflatedNormalizerBlockData Q.1
    letI := data.fintypeBlock
    Navarro408PCoreDefectSource (p := p) Q.1 data.blocks
  mappedContainment : ∀ Q : CharacterWeight.RadicalSubgroup (p := p) (G := G),
    let data := R.1.operations.inflatedNormalizerBlockData Q.1
    letI := R.1.operations.ambientBlockData.fintypeBlock
    letI := data.fintypeBlock
    Navarro413MappedDefectSource (p := p) Q.1
      data.blocks R.1.operations.ambientBlockData.blocks
      data.catalogue R.1.operations.ambientBlockData.catalogue

theorem rawWeight_subgroup_eq_bot
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
    (S : RadicalNormalizerDefectSources R)
    (b : ActualBlock (k := k) (X := G))
    (hZero : letI := R.1.operations.ambientBlockData.fintypeBlock
      IsMaximalCentralBrauerDefect (p := p) R.1.operations.ambientBlockData.blocks b
        (⊥ : Subgroup G))
    (W : CharacterWeight p K G) (hW : R.1.operations.rawWeightBlock W = b) :
    W.subgroup = ⊥ := by
  let O := R.1.operations
  let data := O.inflatedNormalizerBlockData W.subgroup
  let _ := O.ambientBlockData.fintypeBlock
  let _ := data.fintypeBlock
  let q : CharacterWeight.RadicalSubgroup (p := p) (G := G) := ⟨W.subgroup, W.radical⟩
  let c := O.inflateToNormalizer W.subgroup
    (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  have hInd : BlockInducesTo (defectNormalizer W.subgroup)
      data.catalogue O.ambientBlockData.catalogue c b := by
    rw [← hW]
    exact inducedBlock_spec _ data.catalogue O.ambientBlockData.catalogue
      c (O.blockInductionDefined W)
  exact subgroup_eq_bot_of_induces_to_trivial_defect W.subgroup W.radical.isPGroup
    data.blocks O.ambientBlockData.blocks data.catalogue O.ambientBlockData.catalogue
    (S.localExistence q) (S.pCoreContainment q) (S.mappedContainment q) c b hInd hZero

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
