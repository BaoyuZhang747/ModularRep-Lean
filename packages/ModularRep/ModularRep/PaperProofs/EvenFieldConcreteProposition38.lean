import ModularRep.EvenUnipotentIBrBlockAssembly
import ModularRep.PaperProofs.EvenFieldConcreteLemma36

/-!
# Relative endpoint for manuscript Proposition 3.8

This module connects the checked correspondence of manuscript Lemma 3.7 to
the exact `K₀` and block-witness construction for Proposition 3.8.  The group is
the concrete fixed-point carrier used in Lemmas 3.6 and 3.7.  No finite-field
or type-identification theorem is an application hypothesis here.

The conclusion remains relative to the individually exposed cited inputs:
the Lemma 3.6 source package, the parametrisations used in Lemma 3.7, Geck's
integral basic set, the generic-to-Alperin correspondence, the two mark
theorems, and the extension and character-triple clauses of the cyclic outer
criterion.  In particular, this file does not assume an `IBr`-to-weight
bijection or a BAW-good conclusion.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteProposition38

open scoped MonoidAlgebra

open Formalisation
open Formalisation.IBAW
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.EvenUnipotentIBAW
open ModularRep.ManuscriptVerification.EvenUnipotentIBrBlockAssembly
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteLemma36
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters

noncomputable section

/-- Compatibility alias for the field action now owned by the narrow
type-C field-action module. -/
abbrev oppositeFieldAction (r a : ℕ) (ha : 0 < a) :=
  ModularRep.PaperProofs.EvenFieldConcreteTypeC.oppositeFieldAction r a ha

/-- A fixed choice of the correspondence proved to exist in the concrete
relative form of Lemma 3.7.  Selecting the map here makes that lemma, rather
than a separately supplied equivalence, the middle arrow in Proposition 3.8.
-/
noncomputable def selectedLemma36Correspondence
    {A GenericBlock Dual CitedRelativeWeylGroup
      ManuscriptRelativeWeylGroup PairClass : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    [Group ManuscriptRelativeWeylGroup]
    (r a ell : ℕ) (ha : 0 < a)
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A GenericBlock)
    (coherence : InnerCoherence D) (C : GenericBlock)
    (S35 : Inputs (A := A) (Block := GenericBlock) (Dual := Dual)
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
    (cited : CitedData (FiniteSymplecticFixed r a) A GenericBlock Dual ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
      D coherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero) :
    let fixation := lemma_3_5_concrete_relative
      r a ell ha D coherence C S35
    EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
      (W D coherence C)
      (characterOppositeMulAction fixation).smul
      (genericWeightOppositeMulAction fixation).smul :=
  Classical.choice (lemma_3_6_concrete_relative
    r a ell ha D coherence C S35 GeneralisedSeries
    IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
    RelativeWeylGroup IsDefectZero cited)

/-- Application adapter for the kernel-checked construction at the centre of
Proposition 3.8.  It specialises the abstract block-fibre theorem to the
fixed-point carrier and selects the middle arrow from relative Lemma 3.7.

The proof credit belongs to
`EvenUnipotentIBrBlockAssembly.exists_equivariant_blockEquiv_of_stableReduction`.
This adapter does not add proof credit for the standard fixed-point or type
identifications used to interpret the carrier.

Unlike `proposition_3_8_relative` below, this theorem has no cyclic-outer
extension, intermediate-block, character-triple, or `Q = 1` normalisation
input.  Its middle arrow is selected from the checked relative Lemma 3.7.
-/
theorem proposition_3_8_equivariant_bijection_relative
    {A GenericBlock Dual CitedRelativeWeylGroup
      ManuscriptRelativeWeylGroup PairClass K O k ι R Sector Weight DZ : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    [Group ManuscriptRelativeWeylGroup]
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [CharZero K]
    (r a ell : ℕ) (ha : 0 < a) [CharP k ell] [IsAlgClosed k]
    [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)ᵐᵒᵖ] [IsCyclic (FieldGroup a)ᵐᵒᵖ]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A GenericBlock)
    (coherence : InnerCoherence D) (C : GenericBlock)
    (S35 : Inputs (A := A) (Block := GenericBlock) (Dual := Dual)
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
    (cited : CitedData (FiniteSymplecticFixed r a) A GenericBlock Dual ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
      D coherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero)
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [Fintype ι]
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (basicSet : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
        (decompositionMapOfStableReduction Msys iota hcompat))
    [Finite (↑(XC ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))]
    [MulAction (FieldGroup a)ᵐᵒᵖ ι]
    [MulAction (FieldGroup a)ᵐᵒᵖ R]
    [MulAction (FieldGroup a)ᵐᵒᵖ Sector]
    [MulAction (FieldGroup a)ᵐᵒᵖ Weight]
    [MulAction (FieldGroup a)ᵐᵒᵖ DZ]
    [MulAction (FieldGroup a)ᵐᵒᵖ (IBr iota)]
    (Ctx : Context (FieldGroup a)ᵐᵒᵖ ι R Sector
      (IBr iota) Weight DZ)
    (hblock : Ctx.brauerBlock =
      irreducibleBrauerCharacterBlock iota hinj blocks)
    (hstable : IsAutomorphismStableIBrBlock
      (oppositeFieldAction r a ha) iota hinj blocks block)
    [MulAction (FieldGroup a)ᵐᵒᵖ
      (Fibre Ctx.brauerBlock block)]
    [MulAction (FieldGroup a)ᵐᵒᵖ
      (Fibre Ctx.weightBlock block)]
    (hSourceAction : ∀ (sigma : (FieldGroup a)ᵐᵒᵖ)
      (x : Fibre Ctx.brauerBlock block),
      contextBrauerFibreEquiv iota hinj blocks Ctx block hblock (sigma • x) =
        automorphismIBrBlockSmul (oppositeFieldAction r a ha) hstable sigma
          (contextBrauerFibreEquiv iota hinj blocks Ctx block hblock x))
    (genericToAlperin :
      let fixation := lemma_3_5_concrete_relative
        r a ell ha D coherence C S35
      EquivariantEquiv (FieldGroup a)ᵐᵒᵖ (W D coherence C)
        (Fibre Ctx.weightBlock block)
        (genericWeightOppositeMulAction fixation).smul (· • ·))
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{0, 0}
      (p := 2) (A := (FieldGroup a)ᵐᵒᵖ))
    (burnside : PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{0, 0}
      (A := (FieldGroup a)ᵐᵒᵖ)) :
    let fixation := lemma_3_5_concrete_relative
      r a ell ha D coherence C S35
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
      characterOppositeMulAction fixation
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence C) :=
      genericWeightOppositeMulAction fixation
    ∀ hordinary : OrdinaryTwistCompatibleLabels basicSet
        (oppositeFieldAction r a ha),
      Nonempty (EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
        (Fibre Ctx.brauerBlock block) (Fibre Ctx.weightBlock block)
        (· • ·) (· • ·)) := by
  dsimp only
  intro hordinary
  let fixation := lemma_3_5_concrete_relative
    r a ell ha D coherence C S35
  letI : MulAction (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
    characterOppositeMulAction fixation
  letI : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence C) :=
    genericWeightOppositeMulAction fixation
  exact exists_equivariant_blockEquiv_of_stableReduction
    iota hinj blocks block Msys hcompat basicSet
    (oppositeFieldAction r a ha) hstable hordinary
    (ModularRep.isCyclic_quotient_pCore 2 ((FieldGroup a)ᵐᵒᵖ))
    conlon burnside Ctx hblock hSourceAction
    (selectedLemma36Correspondence r a ell ha D coherence C S35
      GeneralisedSeries IsEJGCClass LocalCharacterInEllPrimeSeries
      InducesBlockC RelativeWeylGroup IsDefectZero cited)
    genericToAlperin

/-- Construction-only application wrapper for Proposition 3.8.

The correspondence `X_C → W(C)` is not an argument: it is the selected
output of `lemma_3_6_concrete_relative`.  The full typed block witness still
depends on the supplied cyclic-outer conditions and on the exact `Q = 1`
normalisation.  Those conclusion-adjacent inputs receive no proof credit. -/
theorem proposition_3_8_relative
    {A GenericBlock Dual CitedRelativeWeylGroup
      ManuscriptRelativeWeylGroup PairClass K O k ι R Sector Weight DZ : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    [Group ManuscriptRelativeWeylGroup]
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [CharZero K]
    (r a ell : ℕ) (ha : 0 < a) [CharP k ell] [IsAlgClosed k]
    [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)ᵐᵒᵖ] [IsCyclic (FieldGroup a)ᵐᵒᵖ]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A GenericBlock)
    (coherence : InnerCoherence D) (C : GenericBlock)
    (S35 : Inputs (A := A) (Block := GenericBlock) (Dual := Dual)
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
    (cited : CitedData (FiniteSymplecticFixed r a) A GenericBlock Dual ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
      D coherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero)
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [Fintype ι]
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : ι)
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (basicSet : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
        (decompositionMapOfStableReduction Msys iota hcompat))
    [Finite (↑(XC ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))]
    [MulAction (FieldGroup a)ᵐᵒᵖ ι]
    [MulAction (FieldGroup a)ᵐᵒᵖ R]
    [MulAction (FieldGroup a)ᵐᵒᵖ Sector]
    [MulAction (FieldGroup a)ᵐᵒᵖ Weight]
    [MulAction (FieldGroup a)ᵐᵒᵖ DZ]
    [MulAction (FieldGroup a)ᵐᵒᵖ (IBr iota)]
    (Ctx : Context (FieldGroup a)ᵐᵒᵖ ι R Sector
      (IBr iota) Weight DZ)
    (hblock : Ctx.brauerBlock =
      irreducibleBrauerCharacterBlock iota hinj blocks)
    (hstable : IsAutomorphismStableIBrBlock
      (oppositeFieldAction r a ha) iota hinj blocks block)
    [MulAction (FieldGroup a)ᵐᵒᵖ
      (Fibre Ctx.brauerBlock block)]
    [MulAction (FieldGroup a)ᵐᵒᵖ
      (Fibre Ctx.weightBlock block)]
    (hSourceAction : ∀ (sigma : (FieldGroup a)ᵐᵒᵖ)
      (x : Fibre Ctx.brauerBlock block),
      contextBrauerFibreEquiv iota hinj blocks Ctx block hblock (sigma • x) =
        automorphismIBrBlockSmul (oppositeFieldAction r a ha) hstable sigma
          (contextBrauerFibreEquiv iota hinj blocks Ctx block hblock x))
    (hBrauerAction : FibreActionCompatible
      (E := (FieldGroup a)ᵐᵒᵖ) Ctx.brauerBlock block)
    (hWeightAction : FibreActionCompatible
      (E := (FieldGroup a)ᵐᵒᵖ) Ctx.weightBlock block)
    (genericToAlperin :
      let fixation := lemma_3_5_concrete_relative
        r a ell ha D coherence C S35
      EquivariantEquiv (FieldGroup a)ᵐᵒᵖ (W D coherence C)
        (Fibre Ctx.weightBlock block)
        (genericWeightOppositeMulAction fixation).smul (· • ·))
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{0, 0}
      (p := 2) (A := (FieldGroup a)ᵐᵒᵖ))
    (burnside : PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{0, 0}
      (A := (FieldGroup a)ᵐᵒᵖ))
    (T : CyclicOuterSourceInputs iota Ctx block) :
    let fixation := lemma_3_5_concrete_relative
      r a ell ha D coherence C S35
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
      characterOppositeMulAction fixation
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence C) :=
      genericWeightOppositeMulAction fixation
    ∀ (hordinary : OrdinaryTwistCompatibleLabels basicSet
        (oppositeFieldAction r a ha))
      (hnormalisation : ∀ (d : DZ)
        (hd : Ctx.brauerBlock (Ctx.reduce d) = block),
          ((contextBrauerFibreEquiv iota hinj blocks Ctx block hblock).trans
            ((basicToIBrBlockOfStableReduction iota hinj blocks block Msys
                hcompat basicSet (oppositeFieldAction r a ha) hstable
                hordinary
                (ModularRep.isCyclic_quotient_pCore 2
                  ((FieldGroup a)ᵐᵒᵖ)) conlon burnside).symm.trans
              ((selectedLemma36Correspondence r a ell ha D coherence C S35
                GeneralisedSeries IsEJGCClass
                LocalCharacterInEllPrimeSeries InducesBlockC
                RelativeWeylGroup IsDefectZero cited).toEquiv.trans
                genericToAlperin.toEquiv)))
              ⟨Ctx.reduce d, hd⟩ =
            ⟨Ctx.atOne d, (Ctx.atOne_block d).trans hd⟩),
      Nonempty (BlockWitness Ctx block) := by
  dsimp only
  intro hordinary hnormalisation
  let fixation := lemma_3_5_concrete_relative
    r a ell ha D coherence C S35
  letI : MulAction (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
    characterOppositeMulAction fixation
  letI : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence C) :=
    genericWeightOppositeMulAction fixation
  exact exists_blockWitness_of_stableReduction
    iota hinj blocks block Msys hcompat basicSet
    (oppositeFieldAction r a ha) hstable hordinary
    (ModularRep.isCyclic_quotient_pCore 2 ((FieldGroup a)ᵐᵒᵖ))
    conlon burnside Ctx hblock hSourceAction hBrauerAction hWeightAction
    (selectedLemma36Correspondence r a ell ha D coherence C S35
      GeneralisedSeries IsEJGCClass LocalCharacterInEllPrimeSeries
      InducesBlockC RelativeWeylGroup IsDefectZero cited)
    genericToAlperin T hnormalisation

end

end ModularRep.PaperProofs.EvenFieldConcreteProposition38


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
