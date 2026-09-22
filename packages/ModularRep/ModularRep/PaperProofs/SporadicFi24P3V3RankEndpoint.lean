import ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate
import ModularRep.PaperProofs.SporadicFi24P3QOneSourceFacingWindow

/-!
# Production endpoint for the `Fi'_{24}` prime-three V3 rank certificate

This module is the narrow production adapter for the V3 restriction-row
certificate.  The sole finite-data boundary is
`CanonicalSupplementV3Binding`: sixteen selected entries, two row relations,
and the pointwise identity between the canonical symmetrised rows and the
replayed rows.  It contains no rank, linear-independence, spanning,
fixed-point, character-weight, BAW, or iBAW assertion.

Lean first derives raw row rank four and symmetrised row rank three.  After a
source-facing coordinate evaluation of the literal restriction space is
provided, Lean transports these ranks to that space and derives the
nonprincipal Brauer signature `(4, 2)`.  The last theorem threads the same
derived ranks through the existing source-facing correspondence and the
concrete `Q = 1` extension and intermediate-block window.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3V3RankEndpoint

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.SporadicFi24C2OuterActionFromNonprincipalCensus
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3BlockIndexBindingFromCardinality
open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus
open ModularRep.PaperProofs.SporadicFi24P3PlusRankLiteralBridge
open ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract
open ModularRep.PaperProofs.SporadicFi24P3QOneSourceFacingWindow
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources
open ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

/-! ## Kernel-derived rank consequences -/

variable {K : Type u} [Field K] [CharZero K]

/-- The canonical six restriction rows have rank four.  This is derived from
the V3 packet rather than stored in the canonical binding. -/
theorem raw_row_rank_four
    {E : PrimitiveTwentyNineEncoding K}
    (V3 : CanonicalSupplementV3Binding E) :
    Module.finrank K
        (Submodule.span K (Set.range V3.restrictionRows)) = 4 :=
  V3.rawPacket.rows_finrank_eq_four

/-- The six canonical symmetrised rows have rank three.  Their identification
with the replayed rows is the pointwise source field of the canonical binding;
the rank is a kernel conclusion. -/
theorem symmetrised_row_rank_three
    {E : PrimitiveTwentyNineEncoding K}
    (V3 : CanonicalSupplementV3Binding E) :
    Module.finrank K
        (Submodule.span K
          (Set.range
            (Fi24P3PlusRankReplaySource.allPlusRows
              V3.toPlusRankReplaySource))) = 3 := by
  rw [Fi24P3PlusRankReplaySource.allPlusRows_eq_replayed]
  exact replayedPlusRows_finrank_eq_three

/-! ## Transport to the literal restriction space -/

variable {k X BlockIndex : Type u}
variable [Field k] [CharP k 3] [IsAlgClosed k]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable [Invertible (Fintype.card (Subgroup.center X) : k)]

/-- Once the canonical coordinate evaluation is supplied, both literal ranks
are consequences of the V3 packet.  Neither equality is a premise. -/
theorem literal_rank_pair
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    {E : PrimitiveTwentyNineEncoding K}
    (V3 : CanonicalSupplementV3Binding E)
    (LiteralBinding :
      Fi24P3PlusRankLiteralBinding iota hinj blocks S D
        V3.toPlusRankReplaySource) :
    Module.finrank K (ordinaryRestrictionSpan iota hinj blocks D) = 4 ∧
      Module.finrank K
          (LinearMap.range
            (LinearMap.id +
              BrauerRestrictionSpaceBinding.outerAction
                iota hinj blocks D)) = 3 := by
  exact ⟨
    Fi24P3PlusRankLiteralBinding.literal_restrictionSpan_finrank_eq_four
      iota hinj blocks S D V3.toPlusRankReplaySource LiteralBinding,
    Fi24P3PlusRankLiteralBinding.literal_plusAction_finrank_eq_three
      iota hinj blocks S D V3.toPlusRankReplaySource LiteralBinding⟩

/-- The literal nonprincipal Brauer fibre has four elements, two fixed by the
selected outer involution.  This follows from the two kernel-derived ranks and
the already formalised trace argument. -/
theorem nonprincipal_brauer_signature
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
    (E1 : RoutineTransportInput iota hinj blocks R)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    {E : PrimitiveTwentyNineEncoding K}
    (V3 : CanonicalSupplementV3Binding E)
    (LiteralBinding :
      Fi24P3PlusRankLiteralBinding iota hinj blocks S D
        V3.toPlusRankReplaySource) :
    (Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock),
      Nat.card (Function.fixedPoints
        (nonprincipalBrauerPerm iota hinj blocks E1 S))) = (4, 2) := by
  let Alignment :=
    Fi24P3PlusRankLiteralBinding.toNonprincipalBrauerComputationAlignment
      iota hinj blocks S D V3.toPlusRankReplaySource LiteralBinding
  exact
    SporadicFi24P3NonprincipalCensusFromSources.nonprincipalBrauer_signature
      iota hinj blocks E1 S D Alignment

/-! ## Deepest current source-facing endpoint -/

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

/-- Thread the V3 certificate through the global Fischer correspondence and
the concrete `Q = 1` extension and intermediate-block construction.

The arguments after `V3` are the remaining source and semantic bindings.
In particular, `LiteralBinding` identifies the canonical table coordinates
with the literal restriction space.  No rank, fixed-point count, aggregate
Brauer alignment, character-triple predicate, BAW assertion, or iBAW assertion
is accepted as an input. -/
theorem exists_sourceFacingOmega_with_qOne_spathMatchedBlocks_from_v3
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (E1 : RoutineTransportInput iota hinj blocks R)
    (AD : AnDietrichFi24P3SourceCertificate
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight))
    (Bridge : AnDietrichFi24P3LiteralCarrierBridge
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)
    (hCenter : Subgroup.center X = ⊥)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockInjection : Fi24P3BlockIndexInjectionSource BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockInjection.toBlockIndexBinding)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (DefectZeroCompatibility :
      TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (DefectZeroBlocks : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (DefectZeroSubgroups :
      DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (DefectZeroIdentification :
      Fi24DefectZeroBlockIdentification iota hinj blocks D
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction))
    (RestrictionBinding :
      BrauerRestrictionSpaceBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction))
    {Encoding : PrimitiveTwentyNineEncoding K}
    (V3 : CanonicalSupplementV3Binding Encoding)
    (LiteralBinding :
      Fi24P3PlusRankLiteralBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        RestrictionBinding V3.toPlusRankReplaySource)
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (TableBlockMatch : Fi24P3NamedTableIntervalCentralCharacterMatch
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding
            BlockAction).nonprincipalBlock
        Q table)
    (LocalCensus : Fi24P3LocalDefectZeroCensusBinding R Q table)
    (RadicalSupport : Fi24P3NonprincipalRadicalSupportSource
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        Q table)
    (WeightActionAlignment :
      Fi24P3NonprincipalTable8ActionAlignment
        R
          (fi24ThreeBlockSourceOfBindings
            blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
          Q table S414 TableBlockMatch
          (nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
            R
              (fi24ThreeBlockSourceOfBindings
                blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
              Q table LocalCensus RadicalSupport))
    (hOuterQuotientCard :
      Nat.card
        ((MulAut X)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2)
    (Carrier : QOneDefinition35CarrierSources
      iota hinj blocks R D)
    (Lower : ∀ d :
        GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
      QOneCyclicExtensionBlockSources
        T d
        (qOneDefinition35Brauer iota hinj blocks R D Carrier d)
        (qOneDefinition35Weight iota hinj blocks R D T
          DefectZeroCompatibility Carrier d)
        rfl) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) =
          brauerBlock iota hinj blocks phi) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        let psi := qOneDefinition35Brauer
          iota hinj blocks R D Carrier d
        let w := qOneDefinition35Weight
          iota hinj blocks R D T DefectZeroCompatibility Carrier d
        psi.1 = D.reduce (iota := iota) d ∧
          w.1 = Omega (D.reduce (iota := iota) d) ∧
          Nonempty (@DerivedQOneSpathMatchedBlockData
            (qOneDefinition35Problem iota hinj blocks R D Carrier d)
            T d psi w rfl (Lower d))) := by
  exact
    exists_sourceFacingOmega_with_qOne_spathMatchedBlocks_from_plus_rank_sources
        iota hinj blocks R E1 AD Bridge hCenter Involution BlockInjection
        BlockAction D T DefectZeroCompatibility DefectZeroBlocks
        DefectZeroSubgroups DefectZeroIdentification RestrictionBinding
        V3.toPlusRankReplaySource LiteralBinding Q table S414 TableBlockMatch
        LocalCensus RadicalSupport WeightActionAlignment hOuterQuotientCard
        Carrier Lower

end ModularRep.PaperProofs.SporadicFi24P3V3RankEndpoint


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
