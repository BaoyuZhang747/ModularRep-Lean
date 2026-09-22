import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock

/-! The complete literal prime-three block labels give a one-row ordinary
block. Its actual Brauer span is one-dimensional. The resulting singleton
for every global defect-zero character is derived, not a table field. -/

noncomputable section
set_option maxRecDepth 4096
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryBlocks
open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters

universe u
variable {k K G I : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype I]
variable {e : I → k[G]}
variable (iota : PrimeRegularRootEmbedding 3 k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition e)
variable (Dordinary : ActualOrdinaryDecomposition iota hinj blocks)
variable (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
variable (C : FullOrdinaryDegreeTable K G)
variable (allocation : ∀ r, Dordinary.ordinaryBlock (C.character r) = roles (blockLabels r))

include allocation

theorem selected_ordinary_block_complete :
    ∀ chi, Dordinary.ordinaryBlock chi = roles 2 ↔ chi = C.character 93 := by
  intro chi
  constructor
  · intro hchi
    obtain ⟨r, rfl⟩ := C.complete chi
    have hl : blockLabels r = 2 :=
      roles.injective ((allocation r).symm.trans hchi)
    exact congrArg C.character ((block_label_two_iff r).mp hl)
  · rintro rfl
    exact (allocation 93).trans (congrArg roles ((block_label_two_iff 93).mpr rfl))

theorem selected_brauer_block_card_one :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = roles 2} = 1 := by
  have hcomplete : ∀ chi, Dordinary.ordinaryBlock chi = roles 2 ↔
      ∃ _ : Fin 1, C.character 93 = chi := by
    intro chi
    rw [selected_ordinary_block_complete iota hinj blocks Dordinary roles C allocation chi]
    constructor
    · intro h
      exact ⟨0, h.symm⟩
    · rintro ⟨_, h⟩
      exact h.symm
  have hspan : Submodule.span K
      ({actualOrdinaryRestriction (p := 3) (C.character 93)} :
        Set (PrimeRegularFunction K G 3)) =
      actualBlockBrauerSpan iota hinj blocks (roles 2) := by
    simpa only [Set.range_const] using
      (actualBlockOrdinaryRows_span iota hinj blocks Dordinary (roles 2)
        (fun _ : Fin 1 => C.character 93) hcomplete)
  have hne : actualOrdinaryRestriction (p := 3) (C.character 93) ≠ 0 := by
    intro h
    have h1 := congrFun h (⟨1, isPrimeRegular_one⟩ : PrimeRegularElement (G := G) 3)
    change C.character 93 1 = 0 at h1
    rw [C.degree 93] at h1
    change (178514751987 : K) = 0 at h1
    norm_num at h1
  rw [actualBlockBrauer_card_eq_finrank iota hinj blocks (roles 2), ← hspan]
  exact finrank_span_singleton hne

def fullTableDefectZeroBlockSource
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (Dzero : DefectZeroReductionSource iota) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks Dzero := by
  have hcard := selected_brauer_block_card_one iota hinj blocks Dordinary roles C allocation
  apply canonicalDefectZeroBlockSource iota hinj blocks R Dordinary Dzero
  intro d
  have hd : Dordinary.ordinaryBlock d.val = roles 2 :=
    (selected_ordinary_block_complete iota hinj blocks Dordinary roles C allocation d.val).mpr
      ((defectZero_iff_selected C d.val).mp d.property)
  rw [hd]
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
