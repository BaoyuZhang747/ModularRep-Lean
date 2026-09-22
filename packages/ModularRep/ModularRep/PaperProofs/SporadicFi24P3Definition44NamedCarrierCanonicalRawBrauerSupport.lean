import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizerInducedBrauerSupport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameMapQOne

/-! Each actual raw weight has nonzero ambient Brauer support at its own
radical subgroup. Canonical reduction and block compatibility identify the
normalizer representation; induction and its scalar action supply support. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRawBrauerSupport
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierNormalizerInducedBrauerSupport

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fact p.Prime]

theorem rawWeight_has_nonzero_brauer_support
    (iota : PrimeRegularRootEmbedding p k K G)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (W : CharacterWeight p K G) (source : CanonicalRawReduction iota W) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    HasNonzeroCentralBrauerRestriction R.1.operations.ambientBlockData.blocks
      (R.1.operations.rawWeightBlock W) W.subgroup := by
  let O := R.1.operations
  let data := O.inflatedNormalizerBlockData W.subgroup
  let _ := O.ambientBlockData.fintypeBlock
  let _ := data.fintypeBlock
  let c := O.inflateToNormalizer W.subgroup
    (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  have hInd : BlockInducesTo (defectNormalizer W.subgroup)
      data.catalogue O.ambientBlockData.catalogue c (O.rawWeightBlock W) :=
    inducedBlock_spec _ data.catalogue O.ambientBlockData.catalogue
      c (O.blockInductionDefined W)
  have hlocal : irreducibleBrauerCharacterBlock source.normalizerRoot
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding source.normalizerRoot)
      data.blocks source.localBrauer = c :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer W source
  exact normalizer_induced_block_has_nonzero_brauer_support W.subgroup W.radical.isPGroup
    source.normalizerRoot
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding source.normalizerRoot)
    data.blocks O.ambientBlockData.blocks data.catalogue O.ambientBlockData.catalogue
    source.localBrauer (O.rawWeightBlock W) (by rwa [hlocal])

theorem rawWeight_subgroup_eq_bot_of_canonical_reduction
    (iota : PrimeRegularRootEmbedding p k K G)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (b : ActualBlock (k := k) (X := G))
    (hZero : letI := R.1.operations.ambientBlockData.fintypeBlock
      IsMaximalCentralBrauerDefect (p := p) R.1.operations.ambientBlockData.blocks b
        (⊥ : Subgroup G))
    (W : CharacterWeight p K G) (hW : R.1.operations.rawWeightBlock W = b) :
    W.subgroup = ⊥ := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  have hsupport := rawWeight_has_nonzero_brauer_support iota R compatibility W
    (rawReductionOfAvailability iota availability W)
  rw [hW] at hsupport
  exact (hZero.eq_of_nonzero_le W.subgroup W.radical.isPGroup hsupport bot_le).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRawBrauerSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
