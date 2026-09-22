import ModularRep.PaperProofs.SporadicFi24C2OuterActionFromNonprincipalCensus
import ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus
import ModularRep.PaperProofs.SporadicFi24P3QOneNormalisationFromSources
import ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources

/-!
# The source-facing `Fi'_{24}` prime-three moving-window composite

This module joins the narrow source adapters established in the preceding
prime-three windows.  The three literal blocks are constructed from the role
binding and the selected-outer action binding.  The four-row weight coverage
is derived from the local defect-zero census and radical support.  Lean then
constructs both `Fi24NonprincipalCensusSource` and `C2OuterActionSource`
before applying the block-preserving, full-automorphism-equivariant endpoint
with its `Q = 1` normalisation.

The remaining source boundary is deliberately displayed in the theorem
signature: the literal carrier and block bindings, restriction-space and
rank alignments, local table bindings, corrected Table 8 action alignment,
defect-zero sources, An--Dietrich carrier certificate and bridge, centreless
identification, and the cardinality-two outer quotient.  In particular, no
nonprincipal census record, operational outer-action record, principal map or
signature, blockwise equivalence, BAW statement, or iBAW statement is an
input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3SourceFacingComposite

open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.SporadicFi24C2OuterActionFromNonprincipalCensus
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus
open ModularRep.PaperProofs.SporadicFi24P3QOneNormalisationFromSources
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
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

/-- The complete source-facing endpoint combined from the narrow independent
inputs.  The three composite records consumed by the older endpoint are
constructed in the proof, as is the four-row weight coverage used to build
the nonprincipal census. -/
theorem exists_blockPreservingAutEquivariantEquiv_with_qOne_from_narrow_sources
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
    (BlockBinding : Fi24P3BlockIndexBinding BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockBinding)
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
          blocks Involution BlockBinding BlockAction))
    (RestrictionBinding :
      BrauerRestrictionSpaceBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction))
    (BrauerAlignment :
      Fi24P3NonprincipalBrauerComputationAlignment iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction)
        RestrictionBinding)
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (TableBlockMatch : Fi24P3NamedTableIntervalCentralCharacterMatch
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction).nonprincipalBlock
        Q table)
    (LocalCensus : Fi24P3LocalDefectZeroCensusBinding R Q table)
    (RadicalSupport : Fi24P3NonprincipalRadicalSupportSource
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction)
        Q table)
    (WeightActionAlignment :
      Fi24P3NonprincipalTable8ActionAlignment
        R
          (fi24ThreeBlockSourceOfBindings
            blocks Involution BlockBinding BlockAction)
          Q table S414 TableBlockMatch
          (nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
            R
              (fi24ThreeBlockSourceOfBindings
                blocks Involution BlockBinding BlockAction)
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
  let S : Fi24ThreeBlockSource (k := k) (X := X) :=
    fi24ThreeBlockSourceOfBindings
      blocks Involution BlockBinding BlockAction
  let WeightCoverage : Fi24P3NonprincipalWeightCoverage R S Q table :=
    nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
      R S Q table LocalCensus RadicalSupport
  let NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S :=
    fi24NonprincipalCensusSourceOfIndependentSources
      (R := R) iota hinj blocks E1 S RestrictionBinding BrauerAlignment
        Q table S414 TableBlockMatch WeightCoverage WeightActionAlignment
  let OuterSource : C2OuterActionSource iota S :=
    c2OuterActionSource_of_nonprincipalBrauerComputation
      iota hinj blocks E1 S hOuterQuotientCard
        RestrictionBinding BrauerAlignment
  exact exists_blockPreservingAutEquivariantEquiv_with_qOne_from_sources
    (R := R) iota hinj blocks E1 AD Bridge hCenter D T
      DefectZeroCompatibility DefectZeroBlocks DefectZeroSubgroups
      S DefectZeroIdentification NC OuterSource

end ModularRep.PaperProofs.SporadicFi24P3SourceFacingComposite


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
