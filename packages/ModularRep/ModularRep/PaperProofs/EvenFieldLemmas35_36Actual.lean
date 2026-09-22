import ModularRep.EvenUnipotentCorrespondence
import ModularRep.PaperProofs.EvenFieldConcreteLemma35
import ModularRep.PaperProofs.EvenFieldEJGCPairActual

/-!
# Actual-carrier endpoints for manuscript Lemmas 3.6 and 3.7

The ordinary endpoint is the function-valued complex-character set `X_C`,
and the generic-weight endpoint is the quotient
`EvenFieldFMZGenericPair.W`.  The source map assigning an ordinary character
to its block is still a U-level semantic input: the current library has no
bridge identifying complex ordinary-character blocks with the primitive
modular block-idempotent fibres.  No such identification is claimed here.

For Lemma 3.7, the intermediate FMZ disjoint union is indexed by the orbit
quotient of pairs satisfying `D.inL`.  Complete block catalogues and ordinary
block labels remain E1/U inputs.  The interpretation of `D.inL` and the
block-induction implication proved in FMZ, Proposition 3.24, remain E2/U
inputs.  Every relative Weyl group is the actual character-inertia quotient
of the embedded semantic Levi.  The only correspondence fields below are the
exact cited E2 arrows and cardinality identity.  No endpoint action, endpoint
bijection, ambient block selector, fixedness conclusion, BAW-goodness, or
iBAW assertion is an input.
-/

namespace ModularRep.PaperProofs.EvenFieldLemmas35_36Actual

open ModularRep
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldEJGCPairActual
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35Conclusion
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters

noncomputable section

/-! ## Literal FMZ intermediate carrier -/

/-- Exact published inputs for Lemma 3.7 after the U-level pair semantics
have been instantiated on the orbit and relative-Weyl-group carriers.

The first two theorem fields are Cabanes--Enguehard, Theorem 4.4(i), and
Cabanes--Späth, Theorem 2.8.  The separate group isomorphism identifies the
cited fixed-point relative Weyl group with the literal inertia quotient.
The last two fields are Feng--Malle--Zhang, Theorem 7.5 with equation (7.2),
and the cardinality identity in Section 7.1.  Their applicability, including
the identification of `initial` and maximal extendibility, remains part of
the E2/U instantiation and receives no kernel credit here. -/
structure CitedData
    {H A Block Dual CitedRelativeWeylGroup k : Type}
    [Group H] [Fintype H] [Group Dual]
    [Group CitedRelativeWeylGroup] [MulAction (MulAut H) A]
    (ell : ℕ) [Field k] [CharP k ell] [IsAlgClosed k]
    (InBlock : Irr ℂ H → Prop)
    (Series : Irr ℂ H → Dual → Prop)
    (D : Definitions ℂ H A Block) (coherence : InnerCoherence D)
    (C : Block) (pairs : PairClassSource ell k D)
    (initial : pairs.RestrictedPair C)
    (GeneralisedSeries : Set (Irr ℂ H))
    [Fintype (W D coherence C)]
    [Fintype (pairs.DefectZeroUnion C)] where
  cabanesEnguehardTheorem44 :
    unipotentBlockPart InBlock Series = GeneralisedSeries
  cabanesSpathTheorem28 :
    Irr ℂ CitedRelativeWeylGroup ≃ ↑GeneralisedSeries
  finiteRelativeWeylIdentification :
    pairs.RelativeWeylGroupAt initial.1 ≃* CitedRelativeWeylGroup
  fmzTheorem75 :
    Irr ℂ (pairs.RelativeWeylGroupAt initial.1) ≃
      pairs.DefectZeroUnion C
  fmzWeightCardinality :
    Fintype.card (W D coherence C) =
      Fintype.card (pairs.DefectZeroUnion C)

namespace CitedData

variable
    {H A Block Dual E CitedRelativeWeylGroup k : Type}
    [Group H] [Fintype H] [Group Dual] [Group E]
    [Group CitedRelativeWeylGroup] [MulAction (MulAut H) A]
    {ell : ℕ} [Field k] [CharP k ell] [IsAlgClosed k]
    {InBlock : Irr ℂ H → Prop}
    {Series : Irr ℂ H → Dual → Prop}
    {D : Definitions ℂ H A Block} {coherence : InnerCoherence D}
    {C : Block} {pairs : PairClassSource ell k D}
    {initial : pairs.RestrictedPair C}
    {GeneralisedSeries : Set (Irr ℂ H)}
    [Fintype (W D coherence C)]
    [Fintype (pairs.DefectZeroUnion C)]
    {fieldAction : E →* MulAut H}

/-- The first two manuscript arrows, with the source literally `X_C` and the
middle carrier the character set of the actual initial inertia quotient. -/
def characterToRelativeWeyl
    (source : CitedData
      (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
      ell InBlock Series D coherence C pairs initial GeneralisedSeries)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series) :
    ↑(XC ell InBlock Series) ≃
      Irr ℂ (pairs.RelativeWeylGroupAt initial.1) :=
  (Equiv.setCongr
      (XC_eq_unipotentBlockPart ell InBlock Series
        blockSeries seriesDisjoint)).trans
    ((Equiv.setCongr source.cabanesEnguehardTheorem44).trans
      (source.cabanesSpathTheorem28.symm.trans
        (irrEquivOfMulEquiv
          source.finiteRelativeWeylIdentification).symm))

/-- The final existence-only arrow is constructed from the exact cited
cardinality identity. -/
def defectZeroUnionToWeight
    (source : CitedData
      (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
      ell InBlock Series D coherence C pairs initial GeneralisedSeries) :
    pairs.DefectZeroUnion C ≃ W D coherence C :=
  (Fintype.equivOfCardEq source.fmzWeightCardinality).symm

/-- The literal finite set correspondence before equivariance is attached. -/
def correspondence
    (source : CitedData
      (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
      ell InBlock Series D coherence C pairs initial GeneralisedSeries)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series) :
    ↑(XC ell InBlock Series) ≃ W D coherence C :=
  (source.characterToRelativeWeyl blockSeries seriesDisjoint).trans
    (source.fmzTheorem75.trans source.defectZeroUnionToWeight)

/-- Lemma 3.7 on the literal endpoint and intermediate carriers.  The two
actions are constructed from the exact right transports supplied by Lemma
3.6, and their pointwise triviality proves equivariance of the composite. -/
def equivariantCorrespondence
    (source : CitedData
      (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
      ell InBlock Series D coherence C pairs initial GeneralisedSeries)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series)
    (fixation : FixationConclusion ell InBlock Series D coherence C
      fieldAction) :
    EquivariantEquiv Eᵐᵒᵖ ↑(XC ell InBlock Series) (W D coherence C)
      (characterOppositeMulAction fixation).smul
      (genericWeightOppositeMulAction fixation).smul where
  toEquiv := source.correspondence blockSeries seriesDisjoint
  equivariant := by
    intro sigma chi
    change source.correspondence blockSeries seriesDisjoint
        (characterRightTransport fixation sigma.unop chi) =
      genericWeightRightTransport fixation sigma.unop
        (source.correspondence blockSeries seriesDisjoint chi)
    rw [characterRightTransport_eq_self,
      genericWeightRightTransport_eq_self]

end CitedData

/-! ## Concrete fixed-point and literal character/weight endpoints -/

/-- Lemma 3.6 on the concrete fixed-point group and the literal
sets of characters and generic weights.  The ordinary block
map inside `source35` remains a U-level semantic input. -/
theorem lemma_3_5_actual
    {A Dual ι : Type}
    [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (source35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block) :
    FixationConclusion ell
      (source35.e1e4.toExactProvider r a ell ha).inBlock
      (source35.e1e4.toExactProvider r a ell ha).globalSeries.series
      D coherence block (fieldAction r a ha) := by
  exact lemma_3_5_concrete_relative
    r a ell ha D coherence block source35

/-- Lemma 3.7 on the concrete fixed-point group, the literal complex
set of characters and generic-weight quotient, and the orbit quotient of the
pairs satisfying `D.inL`.  The catalogue interpretation, pair semantics, and
the cited implication from `D.inL` to literal block induction remain graded
external inputs. -/
theorem lemma_3_6_actual
    {A Dual CitedRelativeWeylGroup ι k : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    (r a ell : ℕ) (ha : 0 < a)
    [Field k] [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (source35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    (initial : pairs.RestrictedPair block)
    (GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a)))
    [Fintype (W D coherence block)]
    [Fintype (pairs.DefectZeroUnion block)]
    (cited : CitedData
      (CitedRelativeWeylGroup := CitedRelativeWeylGroup) ell
      (source35.e1e4.toExactProvider r a ell ha).inBlock
      (source35.e1e4.toExactProvider r a ell ha).globalSeries.series
      D coherence block pairs initial GeneralisedSeries) :
    let fixation := lemma_3_5_actual r a ell ha D coherence block source35
    Nonempty (EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (source35.e1e4.toExactProvider r a ell ha).inBlock
        (source35.e1e4.toExactProvider r a ell ha).globalSeries.series))
      (W D coherence block)
      (characterOppositeMulAction fixation).smul
      (genericWeightOppositeMulAction fixation).smul) := by
  let fixation := lemma_3_5_actual r a ell ha D coherence block source35
  exact ⟨cited.equivariantCorrespondence
    (source35.e1e4.toExactProvider r a ell ha).toE1Input
    (source35.e1e4.toExactProvider r a ell ha).globalSeries.toE2Input
    fixation⟩

end

end ModularRep.PaperProofs.EvenFieldLemmas35_36Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
