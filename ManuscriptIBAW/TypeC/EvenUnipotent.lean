import ManuscriptIBAW.TypeC.EvenBasicSet
import ManuscriptIBAW.Characters.CyclotomicOrdinaryLabels
import ManuscriptIBAW.TypeC.PairLabelComparison
import ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual

/-!
# The bijection for a unipotent block in even characteristic

This is the bijection step of Proposition 3.8. The character set, generic
weights, Alperin weights, block maps and field actions are those of the
specified symplectic construction. The map from the ordinary basic set to
irreducible Brauer characters follows from the pointwise fixed basis
argument.

The comparison of the CE and KM block labels uses a common constituent of
the same pair. It determines the initial KM pair and the map in
Feng–Malle–Zhang, Theorem 7.5. The remaining hypotheses and
Feng–Malle–Zhang's Theorem 6.2 are explicit assumptions. The full inductive
condition requires a further application of a criterion.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep
open ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual

open scoped MonoidAlgebra

open Formalisation
open Formalisation.IBAW
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.EvenUnipotentAssembly
open ModularRep.ManuscriptVerification.EvenUnipotentIBAW
open ModularRep.ManuscriptVerification.EvenUnipotentIBrBlockAssembly
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldEJGCPairActual
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters


theorem unipotent_block_equivariant_bijection
    {A Dual CitedRelativeWeylGroup K O k ι : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [CharZero K]
    (r a ell : ℕ) (ha : 0 < a) [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)ᵐᵒᵖ] [IsCyclic (FieldGroup a)ᵐᵒᵖ]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (block : ι)
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    (pairSetting : PairLabelComparison.TypeCSetting
      (H := FiniteSymplecticFixed r a) (ell := ell) r a)
    (ordinaryInBlock : ι → Irr ℂ (FiniteSymplecticFixed r a) → Prop)
    (pairLabels : PairLabelComparison.LabelData D pairs ordinaryInBlock)
    (pairSources : PairLabelComparison.KMCESource D pairs pairLabels pairSetting)
    (initialRaw : RawPair D)
    (initialUnipotent : pairLabels.IsUnipotentECuspidal initialRaw)
    (initialBlock : pairLabels.ceLabel initialRaw = block)
    (ordinaryInBlock_eq : (S35.e1e4.toExactProvider r a ell ha).inBlock =
      ordinaryInBlock block)
    (GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a)))
    [Fintype (W D coherence block)]
    [Fintype (pairs.DefectZeroUnion block)]
    (fmz75 : PairLabelComparison.FMZSource D pairs pairLabels pairSetting)
    (remaining36 : PairLabelComparison.RemainingCitedData D pairs pairLabels coherence
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
        initialRaw block GeneralisedSeries
        (CitedRelativeWeylGroup := CitedRelativeWeylGroup) (InBlock := ordinaryInBlock))
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment D pairs blockIdempotent blockSource)
    (source : ActualBijectionSource
      r a ell ha iota hinj blocks)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
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
    (conductor : ℕ) [NeZero conductor]
    (comparison : Characters.CyclotomicComparison conductor K (FiniteSymplecticFixed r a))
    (realisation : Characters.OrdinaryLabelRealisation comparison
      (fun chi : ↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series) => chi.1)
      basicSet.ordinaryLabel)
    (fmz62 : FMZ62TypeCRestrictedApplication
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed) :
    let fixation :=
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
        r a ell ha D coherence block S35
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
      characterOppositeMulAction fixation
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence block) :=
      genericWeightOppositeMulAction fixation
    let hstable := source.isAutomorphismStableIBrBlock
      ha iota hinj blocks block hfixed
    Nonempty (EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (IBrBlock iota hinj blocks block) (blockSource.Fibre block)
      (automorphismIBrBlockMulAction
        (oppositeFieldAction r a ha) hstable).smul
      (oppositeFieldWeightFibreMulAction
        (r := r) (a := a) ha blockSource block hfixed).smul) := by
  dsimp only
  let fixation :=
    ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
      r a ell ha D coherence block S35
  let _ : MulAction (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
    characterOppositeMulAction fixation
  let _ : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence block) :=
    genericWeightOppositeMulAction fixation
  let _ : MulAction (FieldGroup a)ᵐᵒᵖ ι :=
    oppositeFieldBlockMulAction r a ha
  let _ : MulAction (FieldGroup a)ᵐᵒᵖ (IBr iota) :=
    oppositeFieldIBrMulAction ha iota
  let _ : MulAction (FieldGroup a)ᵐᵒᵖ (ActualWeight ell K r a) :=
    oppositeFieldWeightMulAction r a ell ha K
  have hstable : IsAutomorphismStableIBrBlock
      (oppositeFieldAction r a ha) iota hinj blocks block :=
    source.isAutomorphismStableIBrBlock
      ha iota hinj blocks block hfixed
  let _ : MulAction (FieldGroup a)ᵐᵒᵖ
      (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction (oppositeFieldAction r a ha) hstable
  let _ : MulAction (FieldGroup a)ᵐᵒᵖ
      (blockSource.Fibre block) :=
    oppositeFieldWeightFibreMulAction
      (r := r) (a := a) ha blockSource block hfixed
  have hordinary : OrdinaryTwistCompatibleLabels basicSet (oppositeFieldAction r a ha) :=
    Characters.ordinaryTwistCompatibleLabels comparison (fun chi => chi.1) basicSet realisation
      (oppositeFieldAction r a ha) (by intro sigma chi g; rfl)
  obtain ⟨e, he⟩ := basic_set_brauer_equivariant_bijection
    Msys hcompat basicSet (oppositeFieldAction r a ha) hstable hordinary
    (fun sigma chi => characterRightTransport_eq_self fixation sigma.unop chi)
  let first : EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (IBrBlock iota hinj blocks block)
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
      (· • ·) (· • ·) :=
    equivariantEquivSymm
      (show EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
          (↑(XC ell
            (S35.e1e4.toExactProvider r a ell ha).inBlock
            (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
          (IBrBlock iota hinj blocks block) (· • ·) (· • ·) from
        ⟨e, he⟩)
  let initial := PairLabelComparison.initialPair D pairs pairSetting pairLabels
    pairSources initialRaw initialUnipotent block initialBlock
  let cited := PairLabelComparison.toCitedDataFor D pairs pairSetting pairLabels
    pairSources coherence (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
    initialRaw initialUnipotent block initialBlock GeneralisedSeries fmz75 remaining36
    (S35.e1e4.toExactProvider r a ell ha).inBlock ordinaryInBlock_eq
  let middle := selectedLemma36CorrespondenceActual
    r a ell ha D coherence block S35 pairs initial GeneralisedSeries cited
  obtain ⟨genericToAlperin⟩ :=
    FMZ62TypeCRestrictedApplication.toRestrictedFieldEndpoint
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed
      fmz62
  exact ⟨equivariantEquivTrans
    (equivariantEquivTrans first middle) genericToAlperin⟩


end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
