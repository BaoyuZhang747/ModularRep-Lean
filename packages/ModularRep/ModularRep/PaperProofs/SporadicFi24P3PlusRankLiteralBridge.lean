import ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
import ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract

/-!
# Transporting the `Fi'_{24}` prime-three plus-rank replay to the literal span

The finite replay proves that the symmetrised six-row table matrix has rank
three.  This file states the remaining semantic bridge as an injective
coordinate evaluation of the literal ordinary-restriction span.  The bridge
identifies its image with the raw replayed row span and intertwines the literal
outer action with the printed regular-class permutation.  Lean then transports
the replayed rank to the range of `id + T` on the literal span.

No fixed-point count, Brauer signature, weight datum, character-weight map, or
iBAW conclusion occurs in the bridge.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3PlusRankLiteralBridge

open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

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

/-- The source-facing bridge from the literal restriction span to the thirty
table coordinates used by the finite replay.  Its fields expose an evaluation
map, its injectivity, its complete image, and the pointwise action convention.
They do not state either of the two ranks eventually deduced from them. -/
structure Fi24P3PlusRankLiteralBinding
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (P : Fi24P3PlusRankReplaySource K) : Type u where
  evaluation :
    ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
      (RegularClassIndex → K)
  evaluation_injective : Function.Injective evaluation
  evaluation_range :
    LinearMap.range evaluation =
      Submodule.span K (Set.range P.restrictionRows)
  evaluation_outer :
    ∀ v c,
      evaluation
          (BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D v) c =
        evaluation v (P.regularPermutation c)

namespace Fi24P3PlusRankLiteralBinding

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
theorem evaluation_id_add_outer
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (P : Fi24P3PlusRankReplaySource K)
    (B : Fi24P3PlusRankLiteralBinding iota hinj blocks S D P)
    (v : ordinaryRestrictionSpan iota hinj blocks D) :
    B.evaluation
        (((LinearMap.id :
            ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
              ordinaryRestrictionSpan iota hinj blocks D) +
          BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D) v) =
      plusPullbackLinear P.regularPermutation (B.evaluation v) := by
  ext c
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.map_add,
    Pi.add_apply, plusPullbackLinear]
  rw [B.evaluation_outer]
  rfl

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
theorem mapped_plus_range_eq_replayed_span
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (P : Fi24P3PlusRankReplaySource K)
    (B : Fi24P3PlusRankLiteralBinding iota hinj blocks S D P) :
    (LinearMap.range
        ((LinearMap.id :
            ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
              ordinaryRestrictionSpan iota hinj blocks D) +
          BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D)).map
        B.evaluation =
      Submodule.span K (Set.range (replayedPlusRows (K := K))) := by
  have hmap :
      (LinearMap.range
          ((LinearMap.id :
              ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
                ordinaryRestrictionSpan iota hinj blocks D) +
            BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D)).map
          B.evaluation =
        (LinearMap.range B.evaluation).map
          (plusPullbackLinear P.regularPermutation) := by
    ext y
    constructor
    · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
      refine ⟨B.evaluation v, ⟨v, rfl⟩, ?_⟩
      exact (evaluation_id_add_outer iota hinj blocks S D P B v).symm
    · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
      refine ⟨((LinearMap.id :
          ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
            ordinaryRestrictionSpan iota hinj blocks D) +
          BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D) v,
        ⟨v, rfl⟩, ?_⟩
      exact evaluation_id_add_outer iota hinj blocks S D P B v
  calc
    (LinearMap.range
        ((LinearMap.id :
            ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
              ordinaryRestrictionSpan iota hinj blocks D) +
          BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D)).map
        B.evaluation =
        (LinearMap.range B.evaluation).map
          (plusPullbackLinear P.regularPermutation) := hmap
    _ = (Submodule.span K (Set.range P.restrictionRows)).map
          (plusPullbackLinear P.regularPermutation) := by rw [B.evaluation_range]
    _ = Submodule.span K
          (Set.range (Fi24P3PlusRankReplaySource.allPlusRows P)) :=
      (span_plusRows_eq_map_span P.regularPermutation P.restrictionRows).symm
    _ = Submodule.span K (Set.range (replayedPlusRows (K := K))) := by
      rw [P.allPlusRows_eq_replayed]

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The literal range rank is transported from the finite replay.  It is not a
field of `Fi24P3PlusRankLiteralBinding`. -/
theorem literal_plusAction_finrank_eq_three
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (P : Fi24P3PlusRankReplaySource K)
    (B : Fi24P3PlusRankLiteralBinding iota hinj blocks S D P) :
    Module.finrank K
        (LinearMap.range
          ((LinearMap.id :
              ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
                ordinaryRestrictionSpan iota hinj blocks D) +
            BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D)) = 3 := by
  calc
    Module.finrank K
        (LinearMap.range
          ((LinearMap.id :
              ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
                ordinaryRestrictionSpan iota hinj blocks D) +
            BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D)) =
        Module.finrank K
          ((LinearMap.range
            ((LinearMap.id :
                ordinaryRestrictionSpan iota hinj blocks D →ₗ[K]
                  ordinaryRestrictionSpan iota hinj blocks D) +
              BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D)).map
            B.evaluation) :=
      (Submodule.equivMapOfInjective B.evaluation B.evaluation_injective _).finrank_eq
    _ = Module.finrank K
        (Submodule.span K (Set.range (replayedPlusRows (K := K)))) := by
      rw [mapped_plus_range_eq_replayed_span iota hinj blocks S D P B]
    _ = 3 := replayedPlusRows_finrank_eq_three

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The rank of the literal restriction span is transported from the four
independent `BaseMat` rows in the replay source. -/
theorem literal_restrictionSpan_finrank_eq_four
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (P : Fi24P3PlusRankReplaySource K)
    (B : Fi24P3PlusRankLiteralBinding iota hinj blocks S D P) :
    Module.finrank K (ordinaryRestrictionSpan iota hinj blocks D) = 4 := by
  calc
    Module.finrank K (ordinaryRestrictionSpan iota hinj blocks D) =
        Module.finrank K (LinearMap.range B.evaluation) :=
      (LinearEquiv.ofInjective B.evaluation B.evaluation_injective).finrank_eq
    _ = Module.finrank K
        (Submodule.span K (Set.range P.restrictionRows)) := by
      rw [B.evaluation_range]
    _ = 4 := P.restrictionRows_finrank_eq_four

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Build the earlier computation-alignment interface from the raw restriction
rows and the source-facing finite replay.  Neither rank is an explicit
premise. -/
theorem toNonprincipalBrauerComputationAlignment
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (P : Fi24P3PlusRankReplaySource K)
    (B : Fi24P3PlusRankLiteralBinding iota hinj blocks S D P) :
    Fi24P3NonprincipalBrauerComputationAlignment iota hinj blocks S D where
  restrictionSpan_finrank := by
    have hrank :=
      literal_restrictionSpan_finrank_eq_four iota hinj blocks S D P B
    have hrow := congrArg Prod.fst fi24P3NonprincipalBrauerTranscriptRow_exact
    exact hrank.trans (by simpa using hrow.symm)
  plusAction_finrank := by
    simpa only [fi24P3NonprincipalBrauerPlusRank] using
      literal_plusAction_finrank_eq_three iota hinj blocks S D P B

end Fi24P3PlusRankLiteralBinding

end ModularRep.PaperProofs.SporadicFi24P3PlusRankLiteralBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
