import ModularRep.PaperProofs.SporadicFi24P3PlusRankLiteralBridge
import ModularRep.PaperProofs.SporadicFi24P3BlockIndexBindingFromCardinality
import ModularRep.PaperProofs.SporadicFi24P3SourceFacingComposite

/-!
# The `Fi'_{24}` prime-three composite with the plus rank replayed in Lean

This wrapper removes the aggregate nonprincipal Brauer-computation alignment
from the source-facing composite.  The source-bound inputs replacing it are
the printed finite replay data, a literal-span coordinate binding, and the raw
printed rank of the ordinary-restriction span.

The rank of `id + outerAction` is not source-bound here.  It is proved by the
kernel from the finite replay and the injective literal-span binding.  The
kernel then constructs the old alignment internally and applies the existing
source-facing composite.  Fixed-point counts, census records, operational
outer-action records, BAW or iBAW statements, and the endpoint itself are not
premises.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3PlusRankSourceFacingComposite

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
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24P3SourceFacingComposite
open ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

include E1

/-- The source-facing composite with both restriction-matrix ranks discharged
in the kernel.  `Replay` and `LiteralBinding` remain source-bound; the two
ranks and the aggregate `BrauerAlignment` do not. -/
theorem exists_blockPreservingAutEquivariantEquiv_with_qOne_from_plus_rank_sources
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
    (Replay : Fi24P3PlusRankReplaySource K)
    (LiteralBinding :
      Fi24P3PlusRankLiteralBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        RestrictionBinding Replay)
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
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) =
          brauerBlock iota hinj blocks phi) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) := by
  -- Kernel-proved: the finite replay and literal binding derive both ranks.
  let BrauerAlignment :
      Fi24P3NonprincipalBrauerComputationAlignment iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        RestrictionBinding :=
    Fi24P3PlusRankLiteralBinding.toNonprincipalBrauerComputationAlignment
      iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        RestrictionBinding Replay LiteralBinding
  exact
    exists_blockPreservingAutEquivariantEquiv_with_qOne_from_narrow_sources
      (R := R) iota hinj blocks E1 AD Bridge hCenter Involution
        BlockInjection.toBlockIndexBinding BlockAction D T
        DefectZeroCompatibility DefectZeroBlocks
        DefectZeroSubgroups DefectZeroIdentification RestrictionBinding
        BrauerAlignment Q table S414 TableBlockMatch LocalCensus RadicalSupport
        WeightActionAlignment hOuterQuotientCard

end ModularRep.PaperProofs.SporadicFi24P3PlusRankSourceFacingComposite


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
