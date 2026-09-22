import ManuscriptIBAW.TypeC.EvenUnipotent
import ModularRep.PaperProofs.EvenFieldProposition39HighRankU0

/-!
The assumptions for Proposition 3.8. The pointwise fixed basis argument and
the KM/CE comparison theorem construct each required map. The cited results
remain explicit assumptions.
-/
noncomputable section
namespace ManuscriptIBAW.TypeC.EvenApplication
open scoped MonoidAlgebra Pointwise

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldEJGCPairActual
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldLemmas35_36Actual
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks
open ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
open ModularRep.PaperProofs.EvenFieldProposition39Relative
open ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
open ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven
open ModularRep.PaperProofs.EvenFieldProposition39Sp6Three
open ModularRep.PaperProofs.EvenFieldProposition39Suzuki
open ModularRep.PaperProofs.EvenFieldProposition39TypeA

structure UnipotentInputs (r a ell : ℕ) (ha : 0 < a) where
  A : Type
  Dual : Type
  CitedRelativeWeylGroup : Type
  K : Type
  O : Type
  k : Type
  ι : Type
  [groupDual : Group Dual]
  [fintypeDual : Fintype Dual]
  [groupCitedRelativeWeylGroup : Group CitedRelativeWeylGroup]
  [fieldK : Field K]
  [commRingO : CommRing O]
  [isDomainO : IsDomain O]
  [fieldk : Field k]
  [algebraOK : Algebra O K]
  [charZeroK : CharZero K]
  [charPk : CharP k ell]
  [algClosedk : IsAlgClosed k]
  [fintypeFixed : Fintype (FiniteSymplecticFixed r a)]
  [finiteFieldOpp : Finite (FieldGroup a)ᵐᵒᵖ]
  [cyclicFieldOpp : IsCyclic (FieldGroup a)ᵐᵒᵖ]
  [finiteField : Finite (FieldGroup a)]
  [cyclicField : IsCyclic (FieldGroup a)]
  [mulActionA : MulAction (MulAut (FiniteSymplecticFixed r a)) A]
  [fintypeBlock : Fintype ι]
  [mulActionBlock : MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
  D : Definitions ℂ (FiniteSymplecticFixed r a) A ι
  coherence : InnerCoherence D
  block : ι
  S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
    r a ell ha D coherence block
  pairs : PairClassSource ell k D
  pairSetting : PairLabelComparison.TypeCSetting (H := FiniteSymplecticFixed r a) (ell := ell) r a
  ordinaryInBlock : ι → Irr ℂ (FiniteSymplecticFixed r a) → Prop
  pairLabels : PairLabelComparison.LabelData D pairs ordinaryInBlock
  pairSources : PairLabelComparison.KMCESource D pairs pairLabels pairSetting
  initialRaw : RawPair D
  initialUnipotent : pairLabels.IsUnipotentECuspidal initialRaw
  initialBlock : pairLabels.ceLabel initialRaw = block
  ordinaryInBlock_eq : (S35.e1e4.toExactProvider r a ell ha).inBlock = ordinaryInBlock block
  GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a))
  [fintypeW : Fintype (W D coherence block)]
  [fintypeDefectZeroUnion : Fintype (pairs.DefectZeroUnion block)]
  fmz75 : PairLabelComparison.FMZSource D pairs pairLabels pairSetting
  remaining36 : PairLabelComparison.RemainingCitedData D pairs pairLabels coherence
    (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
    initialRaw block GeneralisedSeries
    (CitedRelativeWeylGroup := CitedRelativeWeylGroup) (InBlock := ordinaryInBlock)
  iota : PrimeRegularRootEmbedding ell k K (FiniteSymplecticFixed r a)
  hinj : IrreducibleBrauerCharacterInjectivity iota
  blockIdempotent : ι → k[FiniteSymplecticFixed r a]
  blocks : BlockIdempotentDecomposition blockIdempotent
  blockSource : LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := FiniteSymplecticFixed r a)
    (Block := ι)
  alignment : AmbientBlockAlignment D pairs blockIdempotent blockSource
  T : FibreTransportSource iota hinj blocks (fieldAction r a ha) block
  Msys : ModularSystem ell K O k
  hcompat : StableReductionBrauerCharacterCompatibility Msys iota
  basicSet : RestrictedIntegralBasicSetOnIBrBlock iota hinj blocks block
    (↑(XC ell (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
    (decompositionMapOfStableReduction Msys iota hcompat)
  [finiteXC : Finite (↑(XC ell
    (S35.e1e4.toExactProvider r a ell ha).inBlock
    (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))]
  conductor : ℕ
  [conductor_neZero : NeZero conductor]
  comparison : Characters.CyclotomicComparison conductor K (FiniteSymplecticFixed r a)
  realisation : Characters.OrdinaryLabelRealisation comparison
    (fun chi : ↑(XC ell (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series) => chi.1)
    basicSet.ordinaryLabel
  fmz62 :
    let hfixed := oppositeFieldBlock_fixed_of_fibreTransport
      (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
      (block := block) (T := T)
    FMZ62TypeCRestrictedApplication
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed
  principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k
  localReduction : ∀ w : LiteralWeightFibre blockSource block,
    SelectedLocalReductionSource blockSource block w

attribute [instance]
  UnipotentInputs.groupDual
  UnipotentInputs.fintypeDual
  UnipotentInputs.groupCitedRelativeWeylGroup
  UnipotentInputs.fieldK
  UnipotentInputs.commRingO
  UnipotentInputs.isDomainO
  UnipotentInputs.fieldk
  UnipotentInputs.algebraOK
  UnipotentInputs.charZeroK
  UnipotentInputs.charPk
  UnipotentInputs.algClosedk
  UnipotentInputs.mulActionA
  UnipotentInputs.fintypeBlock
  UnipotentInputs.mulActionBlock
  UnipotentInputs.fintypeW
  UnipotentInputs.fintypeDefectZeroUnion
  UnipotentInputs.finiteXC
  UnipotentInputs.conductor_neZero


/-- Construct the maps between ordinary characters, Brauer characters and
weights, then apply the semidirect product and cyclic extension results. -/
def UnipotentInputs.endgame {r a ell : ℕ} {ha : 0 < a}
    (source : UnipotentInputs r a ell ha) :
    let _ := source.fintypeFixed
    let _ := source.finiteFieldOpp
    let _ := source.cyclicFieldOpp
    let _ := source.finiteField
    let _ := source.cyclicField
    CyclicEndgameData (iota := source.iota) (hinj := source.hinj) (blocks := source.blocks)
      (phi := fieldAction r a ha) (blockSource := source.blockSource) (block := source.block)
      source.T (canonicalRawNormalizerQuotientInput (p := ell) (K := source.K)
        (H := FiniteSymplecticFixed r a)) source.localReduction := by
  letI := source.fintypeFixed
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  let actual := actualBijectionSourceOfFibreTransport
    (ha := ha) (iota := source.iota) (hinj := source.hinj) (blocks := source.blocks)
    (block := source.block) (T := source.T)
  let hfixed := oppositeFieldBlock_fixed_of_fibreTransport
    (ha := ha) (iota := source.iota) (hinj := source.hinj) (blocks := source.blocks)
    (block := source.block) (T := source.T)
  let omegaOpp := Classical.choice (unipotent_block_equivariant_bijection
    r a ell ha source.block source.D source.coherence source.S35 source.pairs
    source.pairSetting source.ordinaryInBlock source.pairLabels source.pairSources
    source.initialRaw source.initialUnipotent source.initialBlock source.ordinaryInBlock_eq
    source.GeneralisedSeries source.fmz75 source.remaining36 source.iota source.hinj
    source.blocks source.blockSource source.alignment actual hfixed source.Msys
    source.hcompat source.basicSet source.conductor source.comparison source.realisation source.fmz62)
  let omega := rightEquivariantEquivOfOpposite
    (ha := ha) (iota := source.iota) (hinj := source.hinj) (blocks := source.blocks)
    (blockSource := source.blockSource) (block := source.block) (T := source.T) omegaOpp
  exact cyclicEndgameDataOfEquivariantEquiv
    (iota := source.iota) (hinj := source.hinj) (blocks := source.blocks)
    (phi := fieldAction r a ha) (blockSource := source.blockSource) (block := source.block)
    (T := source.T) source.principle
    (canonicalRawNormalizerQuotientInput (p := ell) (K := source.K)
      (H := FiniteSymplecticFixed r a)) source.localReduction omega

end ManuscriptIBAW.TypeC.EvenApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
