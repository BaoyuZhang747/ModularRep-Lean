import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalNormalizedPairs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate

/-!
# One normalized Fischer correspondence with canonical named matched pairs

Call the cancellation theorem once, retaining the explicit canonical V3
binding. Every named clause-(3) and Späth packet uses that same Omega.
The selected reductions are computed from one canonical raw family; the
fixed-root block law is the only local compatibility input. The principal
positive branch is included. At Q=1, the chosen ambient
extensions agree on the actual stored packet. The final representative-level
Definition 4.1 construction remains a separate obligation.
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalFi24Join

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
open ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

open Formalisation ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceCorrespondence
open ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathSource
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalNormalizedPairs

universe u

local instance outerFinite {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

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

theorem exists_normalized_correspondence_with_canonical_named_pairs
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
    (C : ∀ V : CharacterWeight 3 K X, CanonicalRawReduction iota V)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField (fi24ThreeBlockSourceOfBindings blocks Involution
      BlockInjection.toBlockIndexBinding BlockAction))))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 3 k)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 3 k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple 3 k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple 3 k K)
    (seed : ∀ phi : IBr iota, PrimeRegularRootEmbedding 3 k K
      (SelectedBrauerAmbient iota (fi24ThreeBlockSourceOfBindings blocks Involution
      BlockInjection.toBlockIndexBinding BlockAction) phi))
    (fieldSource : SpathCoefficientField 3 k iota.prime)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (catalogues : ∀ (b : ActualBlock (k := k) (X := X))
      (M : EquivariantMatch (blockProblem iota hinj R (canonicalSelectedReduction iota R C) b)),
      BlockCatalogues (blockProblem iota hinj R (canonicalSelectedReduction iota R C) b) M
        (fi24ThreeBlockSourceOfBindings blocks Involution
      BlockInjection.toBlockIndexBinding BlockAction) hCenter M.theta haut) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      ∃ hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
          Omega (alpha • phi) = alpha • Omega phi,
        ∃ hblock : ∀ phi, R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi,
          (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
            Omega (D.reduce (iota := iota) d) = T.atOne d) ∧
          let hblockOps : ∀ phi,
              R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi :=
            fun phi ↦ (hblock phi).trans (operationsBlock_eq iota hinj R blocks phi).symm
          Nonempty (∀ phi : IBr iota,
            let P := problemAt iota hinj R (canonicalSelectedReduction iota R C) phi
            let M := matchAt iota hinj R (canonicalSelectedReduction iota R C) Omega hOmega hblockOps phi
            NormalizedNamedPairWitness P M (fi24ThreeBlockSourceOfBindings blocks Involution
      BlockInjection.toBlockIndexBinding BlockAction) hCenter M.theta haut) := by
  obtain ⟨Omega, hOmega, hblock, hqOne⟩ :=
    exists_blockPreservingAutEquivariantEquiv_with_qOne_from_plus_rank_sources
      (R := R) iota hinj blocks E1 AD Bridge hCenter Involution
      BlockInjection BlockAction D T DefectZeroCompatibility
      DefectZeroBlocks DefectZeroSubgroups DefectZeroIdentification
      RestrictionBinding V3.toPlusRankReplaySource LiteralBinding
      Q table S414 TableBlockMatch LocalCensus RadicalSupport
      WeightActionAlignment hOuterQuotientCard
  refine ⟨Omega, hOmega, hblock, hqOne, ?_⟩
  dsimp only
  let hblockOps : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi :=
    fun phi ↦ (hblock phi).trans (operationsBlock_eq iota hinj R blocks phi).symm
  refine ⟨fun phi ↦ Classical.choice ?_⟩
  let P := problemAt iota hinj R (canonicalSelectedReduction iota R C) phi
  let M := matchAt iota hinj R (canonicalSelectedReduction iota R C) Omega hOmega hblockOps phi
  exact exists_normalized_named_pair_of_canonical_sources
    iota hinj R C (operationsBlock iota hinj R phi) P rfl M
    (fi24ThreeBlockSourceOfBindings blocks Involution
      BlockInjection.toBlockIndexBinding BlockAction) hCenter M.theta haut principle S9295 S9495 S820
    (seed phi) fieldSource compatibility
    (catalogues (operationsBlock iota hinj R phi) M) D T hqOne

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalFi24Join


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
