import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-!
# The reduction of a faithful weight on its prescribed local quotient

Navarro (3.18), pp. 61--62, supplies the irreducible Brauer reduction of
the displayed defect-zero ordinary character. The only source argument below
concerns the actual finite group `NormalizerQuotient W.subgroup`, with enough
ordinary roots and the residue convention of the same modular system.

The canonical local root is the nested restriction of the given ambient
root. Its equality with the direct restriction, and hence its residue
calibration, are proved. The two fields of `CanonicalRawReduction` are then
constructed from the one scoped reduction-existence statement. No principal
block reduction, uniform source over all groups, or whole reduction bundle is
an input. The final theorem applies the existing all-weight specified block
guard to this same reduction; it introduces no second compatibility source.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction

open ModularRep CharacterWeight
open TypeBLocalReductionInstantiation
open TypeBFixedRootDefinitionFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot

variable {K O k X : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group X] [Fintype X]

/-- Nested and direct restriction give the same actual root equivalence. -/
theorem localQuotientRoot_eq_localRoot
    (root : PrimeRegularRootEmbedding 2 k K X) (Q : Subgroup X) :
    localQuotientRoot root Q = TypeBLocalReductionInstantiation.localRoot root Q := by
  unfold localQuotientRoot quotientRoot subgroupRoot
    TypeBLocalReductionInstantiation.localRoot PrimeRegularRootEmbedding.ofCommonRoot
  congr 1

/-- The canonical local root retains the original modular-system calibration. -/
theorem localRoot_residueCanonical
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root) (Q : Subgroup X) :
    RootResidueCompatible Msys (localQuotientRoot root Q) := by
  rw [localQuotientRoot_eq_localRoot]
  exact localRoot_residue Msys root calibration Q

/-- Construct the canonical reduction from Navarro's statement on this one
normalizer quotient. All required local roots are inherited from `X`. -/
def of_scoped
    (Msys : ModularSystem 2 K O k)
    (root : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (W : CharacterWeight 2 K X)
    (source :
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys
        (localQuotientRoot root W.subgroup)
        (localRoot_residueCanonical Msys root calibration W.subgroup)) :
    CanonicalRawReduction root W := by
  letI := localOrdinaryRoots (K := K) W.subgroup
  let result := source.reduction W.localCharacter W.defectZero
  exact ⟨Classical.choose result, Classical.choose_spec result⟩

/-- Inflation across the weight's two-group kernel preserves agreement with
the ambient root on every root needed by the actual normalizer. -/
theorem normalizerRootAt_agrees
    (root : PrimeRegularRootEmbedding 2 k K X)
    (W : CharacterWeight 2 K X) :
    NormalizerRootAgreement root W.subgroup (normalizerRootAt root W) := by
  intro z
  have hexp : primeRegularExponent 2 (NormalizerQuotient W.subgroup) =
      primeRegularExponent 2 (Subgroup.normalizer (W.subgroup : Set X)) :=
    PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq root.prime
      (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set X)))
      W.radical.isPGroup.comap_subtype
  let zQ : rootsOfUnity (primeRegularExponent 2 (NormalizerQuotient W.subgroup)) k :=
    ⟨z.val, by simpa only [hexp] using z.property⟩
  have kernelIsPGroup : IsPGroup 2
      (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set X))) :=
    W.radical.isPGroup.comap_subtype
  have liftEquality :
      (normalizerRootAt root W).lift ((z : kˣ) : k) =
        (localQuotientRoot root W.subgroup).lift ((z : kˣ) : k) :=
    PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
      (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set X)))
      kernelIsPGroup (localQuotientRoot root W.subgroup) ((z : kˣ) : k)
  exact liftEquality.trans (by
    rw [localQuotientRoot_eq_localRoot]
    exact localRoot_agrees root W.subgroup zQ)

/-- The one all-raw-weight guard supplies the specified normalizer block of
this same canonical reduction, without another selected compatibility input. -/
theorem normalizerBlock_of_guarded
    {Block : Type} [MulAction (MulAut X)ᵐᵒᵖ Block]
    {root : PrimeRegularRootEmbedding 2 k K X}
    {operations : LocalBlockInductionOperations
      (p := 2) (k := k) (K := K) (G := X) (Block := Block)}
    (guard : GuardedBlockCompatibility root operations)
    (W : CharacterWeight 2 K X) (reduction : CanonicalRawReduction root W) :
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        operations W.subgroup reduction.normalizerRoot reduction.localBrauer =
      operations.inflateToNormalizer W.subgroup
        (operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero) := by
  apply guard.normalizer_block_of_reduction W reduction.normalizerRoot
    reduction.localBrauer
  · exact normalizerRootAt_agrees root W
  · exact reduction.localBrauer_reduction

end ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
