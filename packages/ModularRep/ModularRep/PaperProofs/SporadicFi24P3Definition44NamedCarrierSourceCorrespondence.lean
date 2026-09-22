import ModularRep.PaperProofs.SporadicFi24P3PlusRankLiteralBridge
import ModularRep.PaperProofs.SporadicFi24P3BlockIndexBindingFromCardinality
import ModularRep.PaperProofs.SporadicFi24C2OuterActionFromNonprincipalCensus
import ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus
import ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources
import ModularRep.PaperProofs.SporadicFi24P3AnDietrichBlockwiseAutomorphismEquiv

/-!
# One Fischer correspondence from the narrow source assemblies

The plus-rank replay constructs the computation alignment; the literal
census constructs the outer action. The existing An--Dietrich cancellation
and automorphism-promotion deduction is called once. Defect-zero uniqueness
then proves Q=1 normalization on that same Omega.

Only the lower source modules are imported. No retained-triple endpoint is
imported or used. The canonical V3 binding is explicit at the Fi24Join caller.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceCorrespondence

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
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichBlockwiseAutomorphismEquiv
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
  let S : Fi24ThreeBlockSource (k := k) (X := X) :=
    fi24ThreeBlockSourceOfBindings blocks Involution
      BlockInjection.toBlockIndexBinding BlockAction
  let WeightCoverage : Fi24P3NonprincipalWeightCoverage R S Q table :=
    nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
      R S Q table LocalCensus RadicalSupport
  let NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S :=
    fi24NonprincipalCensusSourceOfIndependentSources
      (R := R) iota hinj blocks E1 S RestrictionBinding BrauerAlignment
        Q table S414 TableBlockMatch WeightCoverage WeightActionAlignment
  let OuterSource : C2OuterActionSource iota S :=
    c2OuterActionSource_of_nonprincipalBrauerComputation
      iota hinj blocks E1 S hOuterQuotientCard RestrictionBinding BrauerAlignment
  have hcenter : ∀ z : Subgroup.center X, z = 1 := by
    intro z
    apply Subtype.ext
    exact (Subgroup.eq_bot_iff_forall _).mp hCenter z.1 z.2
  obtain ⟨Omega, hOmega, hblock⟩ :=
    exists_blockPreservingAutEquivariantEquiv_from_anDietrich
      iota hinj blocks E1 AD Bridge hcenter D T DefectZeroCompatibility
      DefectZeroBlocks DefectZeroSubgroups S DefectZeroIdentification NC OuterSource
  refine ⟨Omega, hOmega, hblock, ?_⟩
  intro d
  have hpreBlock : brauerBlock iota hinj blocks (Omega.symm (T.atOne d)) =
      brauerBlock iota hinj blocks (D.reduce (iota := iota) d) := by
    rw [← hblock, Omega.apply_symm_apply]
    exact DefectZeroCompatibility.block_atOne d
  have hpre := DefectZeroOrdinaryBlockSource.uniqueBrauer
    (iota := iota) (hinj := hinj) (blocks := blocks)
    D DefectZeroBlocks d (Omega.symm (T.atOne d)) hpreBlock
  rw [← hpre, Omega.apply_symm_apply]
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceCorrespondence



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
