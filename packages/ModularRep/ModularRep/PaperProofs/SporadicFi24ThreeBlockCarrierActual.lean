import Formalisation.BlockCancellation
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Three blocks and their character and weight fibres

This module contains only the literal block fibres, the selected outer
involution, its restricted permutations, and the interface for the two known
fibres in the `Fi'_{24}` cancellation.  It is upstream of the raw sector
family, the global decompositions, and the principal-fibre cancellation.

The block census and `Fi24ThreeKnownEquivalences` remain explicit carrier
interfaces. In the live factory route, the defect-zero field of the latter is
kernel-constructed from D/T/C/B/Z/F, while the nonprincipal field is
kernel-constructed from an external literal census. No principal-block
equivalence, cardinality assertion, combined An--Dietrich map, or iBAW
conclusion is present here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

open Formalisation
open Formalisation.BlockCancellation
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance fi24CarrierCenterFintype :
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

/-! ## Literal block fibres and the selected outer involution -/

/-- The literal Brauer-character fibre over a primitive block idempotent. -/
abbrev BrauerFibre (b : ActualBlock (k := k) (X := X)) :=
  Fibre (brauerBlock iota hinj blocks) b

/-- The literal character-weight fibre over a primitive block idempotent. -/
abbrev WeightFibre (b : ActualBlock (k := k) (X := X)) :=
  Fibre R.1.weightBlock b

/-- A role-labelled census of the three indices in the complete block
decomposition.  It contains no literal block, automorphism, character, weight,
or equivalence data. -/
structure Fi24ThreeBlockIndexCensus (BlockIndex : Type u) where
  principalIndex : BlockIndex
  nonprincipalIndex : BlockIndex
  defectZeroIndex : BlockIndex
  principal_ne_nonprincipal : principalIndex ≠ nonprincipalIndex
  principal_ne_defectZero : principalIndex ≠ defectZeroIndex
  nonprincipal_ne_defectZero : nonprincipalIndex ≠ defectZeroIndex
  all_indices : ∀ i : BlockIndex,
    i = principalIndex ∨ i = nonprincipalIndex ∨ i = defectZeroIndex

/-- The source-shaped identification of the intended outer involution and
the three literal blocks used at the coefficient prime three.  The fields
contain no character-weight equivalence. -/
structure Fi24ThreeBlockSource where
  outer : (MulAut X)ᵐᵒᵖ
  outer_square : outer * outer = 1
  principalBlock : ActualBlock (k := k) (X := X)
  nonprincipalBlock : ActualBlock (k := k) (X := X)
  defectZeroBlock : ActualBlock (k := k) (X := X)
  principal_ne_nonprincipal : principalBlock ≠ nonprincipalBlock
  principal_ne_defectZero : principalBlock ≠ defectZeroBlock
  nonprincipal_ne_defectZero : nonprincipalBlock ≠ defectZeroBlock
  principal_fixed : outer • principalBlock = principalBlock
  nonprincipal_fixed : outer • nonprincipalBlock = nonprincipalBlock
  defectZero_fixed : outer • defectZeroBlock = defectZeroBlock
  all_blocks : ∀ b : ActualBlock (k := k) (X := X),
    b = principalBlock ∨ b = nonprincipalBlock ∨ b = defectZeroBlock

/-- Construct the literal three-block source from a role-labelled census of
the indices in a complete block decomposition and the three fixedness facts.
Distinctness and exhaustiveness of the literal blocks are kernel deductions. -/
def Fi24ThreeBlockSource.ofIndexCensus
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_square : outer * outer = 1)
    (Census : Fi24ThreeBlockIndexCensus BlockIndex)
    (principal_fixed :
      outer • BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
          Census.principalIndex =
        BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
          Census.principalIndex)
    (nonprincipal_fixed :
      outer • BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
          Census.nonprincipalIndex =
        BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
          Census.nonprincipalIndex)
    (defectZero_fixed :
      outer • BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
          Census.defectZeroIndex =
        BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
          Census.defectZeroIndex) :
    Fi24ThreeBlockSource (k := k) (X := X) where
  outer := outer
  outer_square := outer_square
  principalBlock :=
    BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
      Census.principalIndex
  nonprincipalBlock :=
    BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
      Census.nonprincipalIndex
  defectZeroBlock :=
    BlockIdempotentDecomposition.primitiveBlockOfIndex blocks
      Census.defectZeroIndex
  principal_ne_nonprincipal := by
    intro h
    exact Census.principal_ne_nonprincipal
      (BlockIdempotentDecomposition.primitiveBlockOfIndex_injective blocks h)
  principal_ne_defectZero := by
    intro h
    exact Census.principal_ne_defectZero
      (BlockIdempotentDecomposition.primitiveBlockOfIndex_injective blocks h)
  nonprincipal_ne_defectZero := by
    intro h
    exact Census.nonprincipal_ne_defectZero
      (BlockIdempotentDecomposition.primitiveBlockOfIndex_injective blocks h)
  principal_fixed := principal_fixed
  nonprincipal_fixed := nonprincipal_fixed
  defectZero_fixed := defectZero_fixed
  all_blocks := by
    intro b
    obtain ⟨i, rfl⟩ :=
      BlockIdempotentDecomposition.primitiveBlockOfIndex_surjective blocks b
    rcases Census.all_indices i with hi | hi | hi
    · subst i
      exact Or.inl rfl
    · subst i
      exact Or.inr (Or.inl rfl)
    · subst i
      exact Or.inr (Or.inr rfl)

/-- Restriction of the outer action to a fixed literal Brauer block fibre. -/
def brauerFibrePerm
    (_transport : RoutineTransportInput iota hinj blocks R)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (b : ActualBlock (k := k) (X := X))
    (hb : S.outer • b = b) :
    Equiv.Perm (BrauerFibre iota hinj blocks b) :=
  stabilizerFibreEquiv (brauerBlock iota hinj blocks)
    (brauerBlock_transport iota hinj blocks) b S.outer hb

/-- Restriction of the outer action to a fixed literal weight block fibre. -/
def weightFibrePerm
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (b : ActualBlock (k := k) (X := X))
    (hb : S.outer • b = b) :
    Equiv.Perm (WeightFibre (R := R) b) :=
  stabilizerFibreEquiv R.1.weightBlock R.1.weightBlock_transport
    b S.outer hb

def principalBrauerPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (BrauerFibre iota hinj blocks S.principalBlock) :=
  brauerFibrePerm iota hinj blocks E1 S S.principalBlock S.principal_fixed

def nonprincipalBrauerPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (BrauerFibre iota hinj blocks S.nonprincipalBlock) :=
  brauerFibrePerm iota hinj blocks E1 S
    S.nonprincipalBlock S.nonprincipal_fixed

def defectZeroBrauerPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (BrauerFibre iota hinj blocks S.defectZeroBlock) :=
  brauerFibrePerm iota hinj blocks E1 S
    S.defectZeroBlock S.defectZero_fixed

def principalWeightPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (WeightFibre (R := R) S.principalBlock) :=
  weightFibrePerm (R := R) S S.principalBlock S.principal_fixed

def nonprincipalWeightPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (WeightFibre (R := R) S.nonprincipalBlock) :=
  weightFibrePerm (R := R) S
    S.nonprincipalBlock S.nonprincipal_fixed

def defectZeroWeightPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (WeightFibre (R := R) S.defectZeroBlock) :=
  weightFibrePerm (R := R) S S.defectZeroBlock S.defectZero_fixed

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The restricted Brauer-character action is an involution whenever the
selected outer automorphism has order at most two. -/
theorem brauerFibrePerm_involutive
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (b : ActualBlock (k := k) (X := X))
    (hb : S.outer • b = b) :
    Function.Involutive (brauerFibrePerm iota hinj blocks E1 S b hb) := by
  intro phi
  apply Subtype.ext
  simp only [brauerFibrePerm, stabilizerFibreEquiv_coe]
  rw [← mul_smul, S.outer_square, one_smul]

omit [CharP k 3] [IsAlgClosed k]
    [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The restricted weight action is an involution whenever the selected outer
automorphism has order at most two. -/
theorem weightFibrePerm_involutive
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (b : ActualBlock (k := k) (X := X))
    (hb : S.outer • b = b) :
    Function.Involutive (weightFibrePerm (R := R) S b hb) := by
  intro w
  apply Subtype.ext
  simp only [weightFibrePerm, stabilizerFibreEquiv_coe]
  rw [← mul_smul, S.outer_square, one_smul]

/-! ## The independently known block fibres -/

/-- The equivalences on the two block fibres known before cancellation.
There is deliberately no principal-block field. -/
structure Fi24ThreeKnownEquivalences
    (S : Fi24ThreeBlockSource (k := k) (X := X)) where
  nonprincipal :
    BrauerFibre iota hinj blocks S.nonprincipalBlock ≃
      WeightFibre (R := R) S.nonprincipalBlock
  nonprincipal_intertwines :
    Intertwines nonprincipal
      (nonprincipalBrauerPerm iota hinj blocks E1 S)
      (nonprincipalWeightPerm (R := R) S)
  defectZero :
    BrauerFibre iota hinj blocks S.defectZeroBlock ≃
      WeightFibre (R := R) S.defectZeroBlock
  defectZero_intertwines :
    Intertwines defectZero
      (defectZeroBrauerPerm iota hinj blocks E1 S)
      (defectZeroWeightPerm (R := R) S)

end ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
