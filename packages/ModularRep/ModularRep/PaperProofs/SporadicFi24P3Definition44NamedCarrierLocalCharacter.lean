import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedModels
import ModularRep.PrimeRegularRootEmbeddingPQuotient

/-!
# The selected local Brauer character on the literal named base

The radical is a p-group. Its quotient therefore has the same prime-to-p
root exponent as the normaliser, so the selected quotient root convention
inflates without any root-agreement input. Both the actual IBr character
and its affording representation are tied to the chosen weight.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCharacter

open Formalisation ModularRep ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedModels

universe u

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))

local instance outerFinite : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : P.H → P.H))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

abbrev SourceNormalizer := Subgroup.normalizer
  (SelectedRadical P.blockSource P.block M.weight : Set P.H)

/-- The normaliser equivalence follows the actual embedded base inclusion. -/
def normalizerEquivNamedBase : SourceNormalizer P M ≃*
    SporadicFi24P3Definition44NamedCarrierQuotients.LocalBase P M S :=
  (embeddedPairHStabilizerEquivNormalizer
    (selectedOuterField S) P.blockSource P.block M.weight).symm.trans
      (pairBaseEquiv P M S)

theorem namedBaseToQuotient_normalizer (n : SourceNormalizer P M) :
    namedBaseToQuotient P M S (normalizerEquivNamedBase P M S n) =
      normalizerQuotientEquivLocalBase (selectedOuterField S)
        P.blockSource P.block (localQuotientInput P) M.weight (QuotientGroup.mk n) := by
  change rawBaseToQuotient P M S
    ((pairBaseEquiv P M S).symm
      (pairBaseEquiv P M S
        ((embeddedPairHStabilizerEquivNormalizer
          (selectedOuterField S) P.blockSource P.block M.weight).symm n))) = _
  rw [MulEquiv.symm_apply_apply]
  exact subgroupToQuotientImage_embeddedEquiv_symm
    (selectedOuterField S) P.blockSource P.block (localQuotientInput P) M.weight n

theorem normalizerEquivNamedBase_inclusion (n : SourceNormalizer P M) :
    (normalizerEquivNamedBase P M S n).1.1 = xEmbedding P M S n.1 := by
  apply Subtype.ext
  change (((embeddedPairHStabilizerEquivNormalizer
      (selectedOuterField S) P.blockSource P.block M.weight).symm n).1 :
        SelectedOuterAmbient S) = SemidirectProduct.inl n.1
  apply SemidirectProduct.ext
  · have h := embeddedPairHStabilizerEquivNormalizer_coe
      (selectedOuterField S) P.blockSource P.block M.weight
      ((embeddedPairHStabilizerEquivNormalizer
        (selectedOuterField S) P.blockSource P.block M.weight).symm n)
    exact h.symm.trans (congrArg Subtype.val
      ((embeddedPairHStabilizerEquivNormalizer
        (selectedOuterField S) P.blockSource P.block M.weight).apply_symm_apply n))
  · exact (mem_selectedPairBase_iff_right_eq_one P S M.weight _).mp
      ((embeddedPairHStabilizerEquivNormalizer
        (selectedOuterField S) P.blockSource P.block M.weight).symm n).2

theorem selectedOrdinary_inflation (n : SourceNormalizer P M) :
    localOrdinary P M S
      (namedBaseToQuotient P M S (normalizerEquivNamedBase P M S n)) =
    (selectedCharacterWeight P.blockSource P.block M.weight).localCharacter
      (QuotientGroup.mk n) := by
  rw [namedBaseToQuotient_normalizer]
  simp only [localOrdinary, transportedLocalOrdinary,
    OrdinaryIrreducibleCharacter.mapEquiv_apply, MulEquiv.symm_apply_apply]

abbrev RadicalInNormalizer :=
  (SelectedRadical P.blockSource P.block M.weight).subgroupOf (SourceNormalizer P M)

theorem radicalInNormalizer_isPGroup : IsPGroup P.p (RadicalInNormalizer P M) :=
  (Q_radical P M).isPGroup.comap_subtype

def normalizerRoot : PrimeRegularRootEmbedding P.p P.k P.K (SourceNormalizer P M) :=
  PrimeRegularRootEmbeddingPQuotient.ofPQuotient (RadicalInNormalizer P M)
    (radicalInNormalizer_isPGroup P M) (P.localReduction M.weight).iota

def namedLocalRoot : PrimeRegularRootEmbedding P.p P.k P.K
    (SporadicFi24P3Definition44NamedCarrierQuotients.LocalBase P M S) :=
  (normalizerRoot P M).alongMulEquiv (normalizerEquivNamedBase P M S)

theorem namedLocalRoot_lift : (namedLocalRoot P M S).lift = (localRoot P M S).lift := by
  funext z
  calc
    _ = (normalizerRoot P M).lift z :=
      (normalizerRoot P M).alongMulEquiv_lift (normalizerEquivNamedBase P M S) z
    _ = (P.localReduction M.weight).iota.lift z :=
      PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
        (RadicalInNormalizer P M) (radicalInNormalizer_isPGroup P M)
        (P.localReduction M.weight).iota z
    _ = _ := ((P.localReduction M.weight).iota.alongMulEquiv_lift
      (normalizerQuotientEquivLocalBase (selectedOuterField S)
        P.blockSource P.block (localQuotientInput P) M.weight) z).symm

set_option maxHeartbeats 800000 in
/-- The actual irreducible Brauer character (theta*)^0 on the named local base. -/
def namedLocalBrauer : IBr (namedLocalRoot P M S) := by
  refine ⟨PrimeRegularClassFunction.pullback
    (namedBaseToQuotient P M S) (localBrauer P M S).1, ?_⟩
  obtain ⟨W, hW, hchar⟩ := (localBrauer P M S).2
  refine ⟨FDRep.of (Representation.pullback W.ρ (namedBaseToQuotient P M S)),
    hW.pullback _ (namedBaseToQuotient_surjective P M S), ?_⟩
  rw [FDRep.of_ρ', hchar]
  exact (Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
    W.ρ (localRoot P M S) (namedLocalRoot P M S) (namedBaseToQuotient P M S)
      (namedLocalRoot_lift P M S)).symm

theorem localModel_affords_namedBrauer (L : LocalModel P M S) :
    (namedLocalBrauer P M S).1 =
      Representation.brauerCharacterOfRootEmbedding
        (Representation.pullback L.W.ρ (namedBaseToQuotient P M S))
          (namedLocalRoot P M S) := by
  change PrimeRegularClassFunction.pullback _ (localBrauer P M S).1 = _
  rw [L.affords]
  exact (Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
    L.W.ρ (localRoot P M S) (namedLocalRoot P M S) (namedBaseToQuotient P M S)
      (namedLocalRoot_lift P M S)).symm

theorem namedLocalBrauer_reduction (L : LocalModel P M S)
    (z : PrimeRegularElement
      (G := SporadicFi24P3Definition44NamedCarrierQuotients.LocalBase P M S) P.p) :
    localOrdinary P M S (namedBaseToQuotient P M S z.1) =
      (namedLocalBrauer P M S).1 z :=
  L.reduction (PrimeRegularElement.map (namedBaseToQuotient P M S) z)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCharacter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
