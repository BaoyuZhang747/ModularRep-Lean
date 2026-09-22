import ModularRep.BlockIdempotentDecomposition
import ModularRep.WeightCharacterBridge

/-!
# Fixed subgroup normaliser block operations

This file contains only the literal sets of blocks and the three operations
needed at one fixed subgroup `Q`: selection of the quotient block of a defect
zero ordinary character, inflation to the normaliser, and a complete literal
normaliser block decomposition.  It contains no ambient block, block
induction, character weight, or coverage assertion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.CharacterWeight

universe u

variable {p : Nat} {k K G : Type u}
variable [Field k] [Field K] [CharZero K]
variable [Group G] [Fintype G]

local instance localNormalizerSubgroupFintype
    (Q : Subgroup G) : Fintype Q :=
  Fintype.ofFinite Q

/-- A literal block of the local quotient `N_G(Q) / Q`. -/
abbrev LocalQuotientBlock (Q : Subgroup G) :=
  {b : k[NormalizerQuotient Q] // IsPrimitiveCentralIdempotent b}

/-- A literal block of the normaliser `N_G(Q)`. -/
abbrev InflatedNormalizerBlock (Q : Subgroup G) :=
  {b : k[Subgroup.normalizer (Q : Set G)] //
    IsPrimitiveCentralIdempotent b}

/-- The group algebra idempotent underlying a literal normaliser block. -/
def inflatedNormalizerBlockIdempotent (Q : Subgroup G) :
    InflatedNormalizerBlock (k := k) Q →
      k[Subgroup.normalizer (Q : Set G)] :=
  fun b ↦ b.1

/-- A complete literal block decomposition of `N_G(Q)`. -/
structure InflatedNormalizerBlockDecompositionData
    (Q : Subgroup G) where
  [fintypeBlock : Fintype (InflatedNormalizerBlock (k := k) Q)]
  blocks : BlockIdempotentDecomposition
    (inflatedNormalizerBlockIdempotent (k := k) Q)

/-- The quotient block, inflation, and literal normaliser decomposition data
needed at one fixed subgroup `Q`. -/
structure LocalNormalizerBlockOperations
    (Q : Subgroup G) where
  localCharacterBlock :
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)) →
      IsDefectZeroOrdinaryCharacter p chi →
      LocalQuotientBlock (k := k) Q
  inflateToNormalizer :
    LocalQuotientBlock (k := k) Q →
      InflatedNormalizerBlock (k := k) Q
  normalizerBlockData :
    InflatedNormalizerBlockDecompositionData (k := k) Q

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
