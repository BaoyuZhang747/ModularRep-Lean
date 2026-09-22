import ModularRep.EvenUnipotentCorrespondence
import ModularRep.PaperProofs.EvenFieldConcreteLemma35

/-!
# Concrete relative endpoint for manuscript Lemma 3.7

The theorem in this module applies the checked finite set composition of
Lemma 3.7 to the Frobenius fixed-point model of `Sp_(2r)(2^a)`.  Pointwise
fixation of the two endpoint sets is obtained only from the concrete relative
form of Lemma 3.6.
The remaining assumptions are the cited parametrisations and cardinality
identity exposed by `EvenUnipotentCorrespondence.CitedData`.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteLemma36

open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters

noncomputable section

/-- Manuscript Lemma 3.7 on the concrete even-field symplectic group,
relative to the exact E1--E11 package for Lemma 3.6 and to the individually
named cited correspondences used in Lemma 3.7. -/
theorem lemma_3_6_concrete_relative
    {A Block Dual CitedRelativeWeylGroup ManuscriptRelativeWeylGroup
      PairClass : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    [Group ManuscriptRelativeWeylGroup]
    (r a ell : ℕ) (ha : 0 < a)
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A Block)
    (coherence : InnerCoherence D) (C : Block)
    (S35 : Inputs (A := A) (Block := Block) (Dual := Dual)
      r a ell ha D coherence C)
    (GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a)))
    (IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC :
      PairClass → Prop)
    (RelativeWeylGroup :
      RestrictedPairClass PairClass IsEJGCClass
        LocalCharacterInEllPrimeSeries InducesBlockC → Type)
    [∀ p, Group (RelativeWeylGroup p)]
    (IsDefectZero : ∀ p, Irr ℂ (RelativeWeylGroup p) → Prop)
    [Fintype (W D coherence C)]
    [Fintype (DefectZeroUnion RelativeWeylGroup IsDefectZero)]
    (cited : CitedData (FiniteSymplecticFixed r a) A Block Dual ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
      D coherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero) :
    let fixation := lemma_3_5_concrete_relative
      r a ell ha D coherence C S35
    Nonempty (EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
      (W D coherence C)
      (characterOppositeMulAction fixation).smul
      (genericWeightOppositeMulAction fixation).smul) := by
  let fixation := lemma_3_5_concrete_relative
    r a ell ha D coherence C S35
  exact ⟨equivariantCorrespondence cited
      (S35.e1e4.toExactProvider r a ell ha).toE1Input
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.toE2Input
      fixation⟩

end

end ModularRep.PaperProofs.EvenFieldConcreteLemma36


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
