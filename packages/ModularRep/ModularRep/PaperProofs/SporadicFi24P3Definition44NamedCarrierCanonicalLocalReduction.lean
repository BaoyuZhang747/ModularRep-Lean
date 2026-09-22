import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
import ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-! Local reductions and block compatibility in the fixed original root
convention. The generic block law quantifies only over the computed roots.
It does not imply the older law quantified over arbitrary root embeddings. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

def subgroupRoot (iota : PrimeRegularRootEmbedding p k K X) (N : Subgroup X) :
    PrimeRegularRootEmbedding p k K N :=
  PrimeRegularRootEmbedding.ofCommonRoot iota.prime iota.toMulEquiv (by
    simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card N) p)

def localQuotientRoot (iota : PrimeRegularRootEmbedding p k K X) (Q : Subgroup X) :
    PrimeRegularRootEmbedding p k K (NormalizerQuotient Q) :=
  quotientRoot (subgroupRoot iota (Subgroup.normalizer (Q : Set X)))
    (Q.subgroupOf (Subgroup.normalizer (Q : Set X)))

def normalizerRootAt (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X) :
    PrimeRegularRootEmbedding p k K (Subgroup.normalizer (W.subgroup : Set X)) :=
  PrimeRegularRootEmbeddingPQuotient.ofPQuotient
    (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set X)))
    W.radical.isPGroup.comap_subtype (localQuotientRoot iota W.subgroup)

structure CanonicalRawReduction (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X) where
  brauer : IBr (localQuotientRoot iota W.subgroup)
  reduction : IsBrauerReduction (localQuotientRoot iota W.subgroup) W.localCharacter brauer

namespace CanonicalRawReduction

variable {iota : PrimeRegularRootEmbedding p k K X} {W : CharacterWeight p K X}
variable (source : CanonicalRawReduction iota W)

def toRaw : RawReductionSource (k := k) W where
  quotientRoot := localQuotientRoot iota W.subgroup
  quotientBrauer := source.brauer
  quotientReduction := source.reduction

def normalizerRoot := source.toRaw.normalizerRoot

theorem normalizerRoot_eq : source.normalizerRoot = normalizerRootAt iota W := rfl

def localBrauer : IBr source.normalizerRoot := source.toRaw.localBrauer

theorem localBrauer_reduction : NormalizerInflatedReduction W.subgroup W.localCharacter
    source.normalizerRoot source.localBrauer := source.toRaw.localBrauer_reduction

end CanonicalRawReduction

structure CanonicalLocalBlockCompatibility
    (iota : PrimeRegularRootEmbedding p k K X)
    {Block : Type u} [MulAction (MulAut X)ᵐᵒᵖ Block]
    (operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := X) (Block := Block)) : Prop where
  normalizer_block_of_reduction :
    ∀ (W : CharacterWeight p K X) (phiN : IBr (normalizerRootAt iota W)),
      NormalizerInflatedReduction W.subgroup W.localCharacter (normalizerRootAt iota W) phiN →
        NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          operations W.subgroup (normalizerRootAt iota W) phiN =
        operations.inflateToNormalizer W.subgroup
          (operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

namespace CanonicalLocalBlockCompatibility

theorem normalizerBrauerBlock_eq_inflateToNormalizer
    {iota : PrimeRegularRootEmbedding p k K X}
    {Block : Type u} [MulAction (MulAut X)ᵐᵒᵖ Block]
    {operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := X) (Block := Block)}
    (compatibility : CanonicalLocalBlockCompatibility iota operations)
    (W : CharacterWeight p K X) (source : CanonicalRawReduction iota W) :
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      operations W.subgroup source.normalizerRoot source.localBrauer =
    operations.inflateToNormalizer W.subgroup
      (operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero) :=
  compatibility.normalizer_block_of_reduction W source.localBrauer source.localBrauer_reduction

end CanonicalLocalBlockCompatibility

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
