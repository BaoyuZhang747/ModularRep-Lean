import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingleRadicalBlockCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntervalCentralCharacter
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# The four nonprincipal Fischer weights at three

The central character identity first determines the induced block. Four
distinct local characters then give four distinct weights in that block. The
separately published total of four proves that these weights exhaust the
block. No conclusion about radical support or block correspondence is an
input.

The table source is the specified interval central character identity on the
normaliser and ambient block decompositions. Its interpretation uses the six rows of
local block 2 and every fusion candidate returned by `fi24blocks.g`, with
the actual inclusion among those candidates. This identification of the
groups, tables and fusion remains an explicit published, computational and
structural assumption. The number 32 is the length of the returned list and
makes no assertion about an orbit or completeness.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ManuscriptIBAW.Sporadic.Fi24ThreeLocal
open ModularRep ModularRep.CharacterWeight ModularRep.PaperProofs
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

universe u
variable {k K G : Type u}
  [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
  [Group G] [Fintype G]
  (iota : PrimeRegularRootEmbedding 3 k K G)
  (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
  (Q : RadicalSubgroup (p := 3) (G := G))
  (b : ActualBlock (k := k) (X := G))
  (rows : Fin 4 → LocalDefectZeroCharacter (K := K) Q)

local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance normalizerFintype (H : Subgroup G) : Fintype (defectNormalizer H) :=
  Fintype.ofFinite _

/-- Ordinary inflation and central character identities for the specified tables
and primitive block. Neither induced block membership nor a map on the
weight fibre is assumed. -/
structure NamedTableSource where
  normalizerBlock : InflatedNormalizerBlock (k := k) Q.1
  inflation : ∀ r : Fin 4,
    R.1.operations.inflateToNormalizer Q.1
      (R.1.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2) = normalizerBlock
  centralCharacter :
    let localData := R.1.operations.inflatedNormalizerBlockData Q.1
    let I := normalizerCentralBrauerInterval (p := 3) Q.2.isPGroup
    letI := localData.fintypeBlock
    letI := R.1.operations.ambientBlockData.fintypeBlock
    ((localData.catalogue.centralCharacter normalizerBlock).comp
      (centralBrauerMapTo (k := k) (p := 3) Q.1 (defectNormalizer Q.1)
        I.isPGroup I.centralizer_le I.le_normalizer)).toLinearMap =
      (R.1.operations.ambientBlockData.catalogue.centralCharacter b).toLinearMap

/-- The interval theorem applies to the specified blocks. -/
theorem intervalSource : NormalizerIntervalSource R.1.operations Q := by
  let D := R.1.operations.inflatedNormalizerBlockData Q.1
  let : Fintype (defectNormalizer Q.1) := Fintype.ofFinite _
  let := D.fintypeBlock
  exact SporadicFi24P3Definition44NamedCarrierP3IntervalCentralCharacter.interval_central_character_source
    (normalizerCentralBrauerInterval Q.2.isPGroup) D.blocks D.catalogue

variable (table : NamedTableSource R Q b rows)

include table in
/-- Evaluate the supplied central character identity on the target idempotent. -/
theorem intervalEvaluation_one (r : Fin 4) :
    intervalEvaluation R.1.operations Q
      (R.1.operations.inflateToNormalizer Q.1
        (R.1.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2)) b = 1 := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let := (R.1.operations.inflatedNormalizerBlockData Q.1).fintypeBlock
  have h := LinearMap.congr_fun table.centralCharacter
    (R.1.operations.ambientBlockData.blocks.blockIdempotentInCenter b)
  change intervalEvaluation R.1.operations Q table.normalizerBlock b = _ at h
  have hOne := h.trans (R.1.operations.ambientBlockData.catalogue.centralCharacter_own b)
  simpa only [table.inflation r] using hOne

include table in
/-- The selected actual local rows induce weights in the stated block. -/
theorem row_block (r : Fin 4) :
    R.1.weightBlock (classAt iota.prime Q (rows r)) = b := by
  change R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q (rows r)) = b
  exact (rawWeightBlock_eq_iff_intervalEvaluation iota R.1.operations Q (rows r) b
    (intervalSource R Q)).mpr (intervalEvaluation_one R Q b rows table r)

include iota table in
/-- Four distinct induced rows exhaust a block with the independently published
total four. This proves the radical support clause needed by the fixed point
comparison. -/
theorem radical_support
    (rowInjective : Function.Injective rows)
    (weightCount : Nat.card {w : WeightClass (p := 3) (K := K) (X := G) //
      R.1.weightBlock w = b} = 4)
    (w : WeightClass (p := 3) (K := K) (X := G))
    (hw : R.1.weightBlock w = b) :
    radicalClass w = (Quotient.mk'' Q : RadicalConjugacyClass (p := 3) (G := G)) := by
  let fibre := {w : WeightClass (p := 3) (K := K) (X := G) // R.1.weightBlock w = b}
  let : Finite fibre := Nat.finite_of_card_ne_zero (by rw [weightCount]; decide)
  let f : Fin 4 → fibre := fun r =>
    ⟨classAt iota.prime Q (rows r), row_block iota R Q b rows table r⟩
  have hf : Function.Injective f := by
    intro r s h
    apply rowInjective
    exact classAt_injective iota.prime Q (congrArg Subtype.val h)
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, by simpa using weightCount.symm⟩
  obtain ⟨r, hr⟩ := hbij.2 ⟨w, hw⟩
  have hwrow : classAt iota.prime Q (rows r) = w := congrArg Subtype.val hr
  rw [← hwrow]
  rfl

end ManuscriptIBAW.Sporadic.Fi24ThreeLocal

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
