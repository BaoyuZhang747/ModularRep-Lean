import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
import ModularRep.PaperProofs.SubgroupQuotientImage

/-!
# Local representation inflation for cyclic outer actions

This module contains only the representation-level passage from a quotient
local extension to the literal pair stabiliser.  It contains no cyclic
endgame data, block equality, BAW, or iBAW conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (phi : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- The exact local representation-extension conclusion for a selected
literal weight representative. -/
abbrev LocalExtensionConclusion
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) : Prop :=
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  ∃ W : FDRep k (LocalBase phi blockSource block quotientInput w),
    Representation.IsIrreducible W.ρ ∧
    (transportedLocalBrauer
      phi blockSource block quotientInput w source).1 =
      Representation.brauerCharacterOfRootEmbedding W.ρ
        (transportedLocalRootEmbedding
          phi blockSource block quotientInput w source) ∧
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      (transportedLocalRootEmbedding
        phi blockSource block quotientInput w source)
      (transportedLocalOrdinary
        phi blockSource block quotientInput w)
      (transportedLocalBrauer
        phi blockSource block quotientInput w source) ∧
    Nonempty (Representation.Extension
      (LocalBase phi blockSource block quotientInput w) W.ρ)

end ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

namespace ModularRep.PaperProofs.EvenFieldFLZ318SelfCover

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

universe u

section QuotientExtensionInflation

variable {R D V : Type u}
variable [Field R] [Group D] [AddCommGroup V] [Module R V]
variable (Q N : Subgroup D) [Q.Normal]

/-- Pull an extension from `D / Q` back to `D`.  Its restriction is the
pullback of the original representation along `N → NQ/Q`. -/
def inflateQuotientExtension
    (rho : Representation R (QuotientImage Q N) V)
    (extension : Representation.Extension (QuotientImage Q N) rho) :
    Representation.Extension N
      (Representation.pullback rho (subgroupToQuotientImage Q N)) where
  representation :=
    Representation.pullback extension.representation (QuotientGroup.mk' Q)
  restrictionEquiv := by
    rw [Representation.pullback_comp]
    have hcomp :
        (QuotientImage Q N).subtype.comp (subgroupToQuotientImage Q N) =
          (QuotientGroup.mk' Q).comp N.subtype := by
      ext n
      rfl
    rw [← hcomp, ← Representation.pullback_comp]
    exact extension.restrictionEquiv.pullback
      (subgroupToQuotientImage Q N)

end QuotientExtensionInflation

section LocalExtensionInflation

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (phi : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (quotientInput : RawNormalizerQuotientInput
  (p := p) (K := K) (H := H))

/-- The quotient extension inflated to the literal pair stabiliser. -/
abbrev InflatedLocalRepresentationExtensionConclusion
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) : Prop :=
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  ∃ W : FDRep k (LocalBase phi blockSource block quotientInput w),
    Representation.IsIrreducible W.ρ ∧
    (transportedLocalBrauer
      phi blockSource block quotientInput w source).1 =
      Representation.brauerCharacterOfRootEmbedding W.ρ
        (transportedLocalRootEmbedding
          phi blockSource block quotientInput w source) ∧
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      (transportedLocalRootEmbedding
        phi blockSource block quotientInput w source)
      (transportedLocalOrdinary
        phi blockSource block quotientInput w)
      (transportedLocalBrauer
        phi blockSource block quotientInput w source) ∧
    Nonempty (Representation.Extension
      (EmbeddedPairHStabilizer phi blockSource block w)
      (Representation.pullback W.ρ
        (subgroupToQuotientImage
          (EmbeddedRadical phi blockSource block quotientInput w)
          (EmbeddedPairHStabilizer phi blockSource block w))))

/-- Inflate a quotient-level local extension to the literal pair
stabiliser. -/
theorem inflate_localExtensionConclusion
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w)
    (hlocal : LocalExtensionConclusion
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w source) :
    InflatedLocalRepresentationExtensionConclusion
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w source := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  rcases hlocal with ⟨W, hW, hcharacter, hreduction, ⟨extension⟩⟩
  exact ⟨W, hW, hcharacter, hreduction,
    ⟨inflateQuotientExtension
      (EmbeddedRadical phi blockSource block quotientInput w)
      (EmbeddedPairHStabilizer phi blockSource block w) W.ρ extension⟩⟩

end LocalExtensionInflation

end ModularRep.PaperProofs.EvenFieldFLZ318SelfCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
