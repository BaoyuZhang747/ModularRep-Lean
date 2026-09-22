import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
import ModularRep.PaperProofs.SubgroupQuotientImage

/-!
# The embedded pair stabiliser and the local normaliser

This module contains the group-theoretic identifications between the
restricted stabiliser of a selected character weight, its embedded copy in
the full pair stabiliser, and the normaliser of the selected radical
subgroup.  It is upstream of character-extension and block-matching data.
-/

noncomputable section

namespace ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- For the selected pair, its stabiliser inside `H` is the normaliser of
its radical subgroup. -/
theorem pairHStabilizer_eq_normalizer
    (w : LiteralWeightFibre blockSource block) :
    PairHStabilizer field blockSource block w =
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) := by
  simpa only [rawSubgroup_selectedRawWeight] using
    (actual_rawWeight_embeddedStabilizer_eq_normalizer
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      field (selectedRawWeight blockSource block w))

/-- The corresponding equivalence of underlying groups. -/
def pairHStabilizerEquivNormalizer
    (w : LiteralWeightFibre blockSource block) :
    PairHStabilizer field blockSource block w ≃*
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) :=
  MulEquiv.subgroupCongr
    (pairHStabilizer_eq_normalizer field blockSource block w)

@[simp]
theorem pairHStabilizerEquivNormalizer_coe
    (w : LiteralWeightFibre blockSource block)
    (h : PairHStabilizer field blockSource block w) :
    ((pairHStabilizerEquivNormalizer field blockSource block w h :
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H)) : H) = h := by
  exact MulEquiv.subgroupCongr_apply
    (pairHStabilizer_eq_normalizer field blockSource block w) h

/-- The canonical inclusion identifies the restricted stabiliser with its
range in the full pair stabiliser. -/
def pairHStabilizerEquivEmbedded
    (w : LiteralWeightFibre blockSource block) :
    PairHStabilizer field blockSource block w ≃*
      EmbeddedPairHStabilizer field blockSource block w := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction field
  letI : MulAction (H ⋊[field] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction field
  exact MulEquiv.ofBijective
    (inlStabilizerHom
      (phi := field) (selectedRawWeight blockSource block w)).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (inlStabilizerHom_injective
          (phi := field) (selectedRawWeight blockSource block w)),
      (inlStabilizerHom
        (phi := field)
        (selectedRawWeight blockSource block w)).rangeRestrict_surjective⟩

@[simp]
theorem pairHStabilizerEquivEmbedded_coe
    (w : LiteralWeightFibre blockSource block)
    (h : PairHStabilizer field blockSource block w) :
    (((pairHStabilizerEquivEmbedded field blockSource block w h :
      EmbeddedPairHStabilizer field blockSource block w) :
        PairStabilizer field blockSource block w) : H ⋊[field] E) =
      SemidirectProduct.inl h.1 := by
  rfl

/-- The embedded copy of the restricted stabiliser is equivalent to the
normaliser of the selected radical. -/
def embeddedPairHStabilizerEquivNormalizer
    (w : LiteralWeightFibre blockSource block) :
    EmbeddedPairHStabilizer field blockSource block w ≃*
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) :=
  (pairHStabilizerEquivEmbedded field blockSource block w).symm.trans
    (pairHStabilizerEquivNormalizer field blockSource block w)

@[simp]
theorem embeddedPairHStabilizerEquivNormalizer_coe
    (w : LiteralWeightFibre blockSource block)
    (h : EmbeddedPairHStabilizer field blockSource block w) :
    ((embeddedPairHStabilizerEquivNormalizer
      field blockSource block w h :
        Subgroup.normalizer
          (SelectedRadical blockSource block w : Set H)) : H) =
      ((h : PairStabilizer field blockSource block w) : H ⋊[field] E).left := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction field
  letI : MulAction (H ⋊[field] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction field
  rcases h with ⟨_, ⟨x, rfl⟩⟩
  have hx :
      (⟨inlStabilizerHom
          (phi := field) (selectedRawWeight blockSource block w) x,
        ⟨x, rfl⟩⟩ : EmbeddedPairHStabilizer field blockSource block w) =
        pairHStabilizerEquivEmbedded field blockSource block w x := by
    apply Subtype.ext
    rfl
  rw [hx]
  simp [embeddedPairHStabilizerEquivNormalizer]

/-- The normaliser equivalence commutes with the quotient maps on the
embedded local base. -/
theorem subgroupToQuotientImage_embeddedEquiv_symm
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        quotientInput w
    ∀ n : Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H),
      subgroupToQuotientImage
          (EmbeddedRadical field blockSource block quotientInput w)
          (EmbeddedPairHStabilizer field blockSource block w)
          ((embeddedPairHStabilizerEquivNormalizer
            field blockSource block w).symm n) =
        normalizerQuotientEquivLocalBase
          field blockSource block quotientInput w (QuotientGroup.mk n) := by
  letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := field) (blockSource := blockSource) (block := block)
      quotientInput w
  intro n
  rw [normalizerQuotientEquivLocalBase_mk]
  apply Subtype.ext
  change QuotientGroup.mk'
      (EmbeddedRadical field blockSource block quotientInput w)
      (((embeddedPairHStabilizerEquivNormalizer
          field blockSource block w).symm n :
            EmbeddedPairHStabilizer field blockSource block w) :
        PairStabilizer field blockSource block w) =
    QuotientGroup.mk'
      (EmbeddedRadical field blockSource block quotientInput w)
      (normalizerToPairStabilizer
        field blockSource block quotientInput w n)
  apply congrArg
  apply Subtype.ext
  apply SemidirectProduct.ext
  · simpa using
      (embeddedPairHStabilizerEquivNormalizer_coe
        field blockSource block w
          ((embeddedPairHStabilizerEquivNormalizer
            field blockSource block w).symm n)).symm
  · rcases ((embeddedPairHStabilizerEquivNormalizer
        field blockSource block w).symm n).2 with ⟨h, hh⟩
    have hright := congrArg
      (fun z : PairStabilizer field blockSource block w ↦
        ((z : H ⋊[field] E).right)) hh
    simpa [inlStabilizerHom] using hright.symm

/-- The quotient map for the selected radical subgroup. -/
def selectedNormalizerQuotientHom
    (w : LiteralWeightFibre blockSource block) :
    Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) →*
      NormalizerQuotient (SelectedRadical blockSource block w) :=
  QuotientGroup.mk'
    ((SelectedRadical blockSource block w).subgroupOf
      (Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H)))

end ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
