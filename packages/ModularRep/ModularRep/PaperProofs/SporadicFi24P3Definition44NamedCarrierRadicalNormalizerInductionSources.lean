import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment

/-! Only local defect existence and mapped defect containment remain as
external normalizer foundations. P-core containment is derived from the
actual modular group algebra, without an additional support premise. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalNormalizerInductionSources
open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport
open SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment
universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fact p.Prime]

structure RadicalNormalizerInductionSources
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G)) : Prop where
  localExistence : ∀ Q : CharacterWeight.RadicalSubgroup (p := p) (G := G),
    let data := R.1.operations.inflatedNormalizerBlockData Q.1
    letI := data.fintypeBlock
    Navarro417LocalDefectExistenceSource (p := p) Q.1 data.blocks
  mappedContainment : ∀ Q : CharacterWeight.RadicalSubgroup (p := p) (G := G),
    let data := R.1.operations.inflatedNormalizerBlockData Q.1
    letI := R.1.operations.ambientBlockData.fintypeBlock
    letI := data.fintypeBlock
    Navarro413MappedDefectSource (p := p) Q.1
      data.blocks R.1.operations.ambientBlockData.blocks
      data.catalogue R.1.operations.ambientBlockData.catalogue

theorem toDefectSources
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
    (S : RadicalNormalizerInductionSources R) :
    RadicalNormalizerDefectSources R := by
  refine ⟨S.localExistence, ?_, S.mappedContainment⟩
  intro Q
  let data := R.1.operations.inflatedNormalizerBlockData Q.1
  let _ := data.fintypeBlock
  exact navarro408PCoreDefectSource Q.1 data.blocks

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalNormalizerInductionSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
