import ModularRep.BrauerReduction
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.LocalNormalizerBrauerBlock

/-!
# Local reduction and inflation block compatibility

Let `W` be a character weight and let `phiN` be an irreducible Brauer
character of the normaliser of its radical subgroup.  This file isolates the
exact source input needed to identify the literal block of `phiN` when it is
the reduction of the ordinary inflation of `W.localCharacter`.

The roles of the source results are distinct.  Navarro's Theorem (3.18)
supplies the irreducible Brauer reduction of the defect-zero quotient
character.  The actual normaliser Brauer character and its literal reduction
equality remain separate theorem inputs below.  Navarro's Theorem (3.3)
supplies decomposition support once that reduction is present.  Passing from
that support statement to the literal primitive-central-idempotent block
selector also uses Navarro's Theorem (3.11) and Lemma (3.13)(b).  Matching the
quotient block label, its inflation, and the literal primitive-idempotent
catalogue remains the E1/U source law.  Theorem (3.3) alone does not make this
carrier identification.  Generic quotient containment alone does not provide
a reverse idempotent-inflation map or a block bisection.
-/

noncomputable section

namespace ModularRep.NavarroLocalReductionInflationBlockCompatibility

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero

universe u

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]

/-- The literal normaliser block containing an irreducible Brauer character.
This forwards the full operations package to its fixed-subgroup projection
and the kernel selector defined on that smaller interface. -/
def normalizerBrauerBlock
    (operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : Subgroup G)
    (iota : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (Q : Set G)))
    (phi : IBr iota) : InflatedNormalizerBlock (k := k) Q :=
  LocalNormalizerBlockOperations.normalizerBrauerBlock
    (operations.toLocalNormalizerBlockOperations Q) iota phi

/-- Exact E1/U compatibility needed for the local block calculation.

This is an operations-wide law on raw character weights.  Its sole field
identifies the literal normaliser block of an actual inflated reduction.  It
does not construct the reduction and does not select any ambient block. -/
structure Source
    (operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block)) : Prop where
  normalizer_block_of_reduction :
    ∀ (W : CharacterWeight p K G)
      (iotaN : PrimeRegularRootEmbedding p k K
        (Subgroup.normalizer (W.subgroup : Set G)))
      (phiN : IBr iotaN),
      NormalizerInflatedReduction W.subgroup W.localCharacter iotaN phiN →
        normalizerBrauerBlock operations W.subgroup iotaN phiN =
          operations.inflateToNormalizer W.subgroup
            (operations.localCharacterBlock
              W.subgroup W.localCharacter W.defectZero)

namespace Source

/-- Apply the source law to a separately supplied literal reduction
identity. -/
theorem normalizerBrauerBlock_eq_inflateToNormalizer
    {operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block)}
    (source : Source operations)
    (W : CharacterWeight p K G)
    (iotaN : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (W.subgroup : Set G)))
    (phiN : IBr iotaN)
    (hReduction : NormalizerInflatedReduction
      W.subgroup W.localCharacter iotaN phiN) :
    normalizerBrauerBlock operations W.subgroup iotaN phiN =
      operations.inflateToNormalizer W.subgroup
        (operations.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero) :=
  Source.normalizer_block_of_reduction source W iotaN phiN hReduction

end Source

end ModularRep.NavarroLocalReductionInflationBlockCompatibility


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
