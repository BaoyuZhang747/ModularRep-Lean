import ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding

/-!
# A primitive-block family on the actual exceptional-cover carrier

The constructor is generic in a finite group H. Its blocks are literal
primitive idempotents, its Brauer convention is the same modular system's
group root, and its local reductions are the existing selected reductions
from the scoped Navarro (3.18) input. The acting groups are the full actual
opposite-automorphism block stabilizers.

The specified local block guard is derived by the accepted ordinary
inflation and decomposition-support construction. The input catalogue
contains only primitive blocks, ordinary local operations and their
ambient idempotent identification. No character matching or full block
condition is supplied. Ordinary coefficients need roots for |H|; only
the residue field has an algebraic-closure hypothesis.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBExceptionalPrimitiveFamilySplitting

open ModularRep FDRepSimpleClassKZero CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open TypeBFixedRootDefinitionFamily TypeBLocalReductionInstantiation
open TypeBLocalPhysicalBlockBinding TypeBModularGroupRootBinding

/-- The specified primitive catalogue and the same local weight operations. -/
structure PrimitiveBlockData (ell : ℕ) (k K H : Type)
    [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
    [Group H] [Fintype H] [Fintype (LiteralPrimitiveBlock k H)] where
  blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k H => b.1)
  blockSource : LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := H)
    (Block := LiteralPrimitiveBlock k H)
  idempotent : ∀ b : LiteralPrimitiveBlock k H,
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1

section Family

variable {ell : ℕ} {k K O H : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  [Group H] [Fintype H] [Fintype (LiteralPrimitiveBlock k H)]
  (Msys : ModularSystem ell K O k)
  [HasEnoughRootsOfUnity K (Nat.card H)]
  (data : PrimitiveBlockData ell k K H)
  (navarro : ∀ (T : Type) [Group T] [Finite T]
    [HasEnoughRootsOfUnity K (Nat.card T)]
    (iota : PrimeRegularRootEmbedding ell k K T)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The family is computed on H itself from one specified coefficient system. -/
def primitiveFamily : Definition35Family ell where
  ellPrime := Msys.prime
  k := k
  K := K
  H := H
  Block := LiteralPrimitiveBlock k H
  blockIdempotent b := b.1
  iota := groupRoot Msys H
  irreducibleBrauerInjective :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
  blocks := data.blocks
  blockSource := data.blockSource
  brauerBlock_transport := primitiveBrauerBlock_transport (groupRoot Msys H)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) data.blocks
  automorphisms := primitiveBlockAutomorphisms
  localReduction := selectedReduction Msys (groupRoot Msys H)
    (groupRoot_residue Msys H) navarro data.blockSource

@[simp]
theorem primitiveFamily_H : (primitiveFamily Msys data navarro).H = H := rfl

@[simp]
theorem primitiveFamily_Block :
    (primitiveFamily Msys data navarro).Block = LiteralPrimitiveBlock k H := rfl

@[simp]
theorem primitiveFamily_iota :
    (primitiveFamily Msys data navarro).iota = groupRoot Msys H := rfl

@[simp]
theorem primitiveFamily_blocks :
    (primitiveFamily Msys data navarro).blocks = data.blocks := rfl

@[simp]
theorem primitiveFamily_blockSource :
    (primitiveFamily Msys data navarro).blockSource = data.blockSource := rfl

/-- Both catalogues assign the very same specified primitive idempotent. -/
theorem primitiveFamily_idempotent (b : LiteralPrimitiveBlock k H) :
    (primitiveFamily Msys data navarro).blockSource.operations.ambientBlockData.blockIdempotent b =
      (primitiveFamily Msys data navarro).blockIdempotent b :=
  data.idempotent b

@[simp]
theorem primitiveFamily_localReduction (b : LiteralPrimitiveBlock k H)
    (w : LiteralWeightFibre data.blockSource b) :
    (primitiveFamily Msys data navarro).localReduction b w =
      selectedReduction Msys (groupRoot Msys H) (groupRoot_residue Msys H)
        navarro data.blockSource b w := rfl

/-- The selected quotient root agrees with the same constructed global root. -/
theorem primitiveFamily_rootAgreement (b : LiteralPrimitiveBlock k H)
    (w : LiteralWeightFibre data.blockSource b) :
    QuotientRootAgreement (G := H) (primitiveFamily Msys data navarro).iota
      (SelectedRadical (H := H) data.blockSource b w)
      ((primitiveFamily Msys data navarro).localReduction b w).iota :=
  selectedReduction_rootAgreement Msys (groupRoot Msys H)
    (groupRoot_residue Msys H) navarro data.blockSource b w

/-- Ordinary inflation membership and specified support derive the full guard. -/
def primitiveFamily_blockCompatibility
    (expansion : ∀ (T : Type) [Group T] [Finite T]
      [HasEnoughRootsOfUnity K (Nat.card T)],
        ScopedDecompositionExpansionSource (H := T) Msys)
    (ordinary : ∀ Q : Subgroup H,
      NormalizerOrdinarySource Msys data.blockSource.operations Q)
    (membership : OrdinaryInflationMembership Msys data.blockSource.operations ordinary) :
    GuardedBlockCompatibility (primitiveFamily Msys data navarro).iota
      (primitiveFamily Msys data navarro).blockSource.operations :=
  guardedBlockCompatibility Msys data.blockSource.operations (groupRoot Msys H)
    (groupRoot_residue Msys H) expansion ordinary membership

/-- The family uses the actual full block stabilizer without transport. -/
def primitiveFamily_stabilizerAdapter (b : LiteralPrimitiveBlock k H) :
    Definition35AutomorphismStabilizerAdapter
      ((primitiveFamily Msys data navarro).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (inverseOpHom_primitiveStabilizerHom b a).symm

@[simp]
theorem primitiveFamily_inverseOpHom (b : LiteralPrimitiveBlock k H)
    (a : PrimitiveBlockStabilizer b) :
    inverseOpHom ((primitiveFamily Msys data navarro).problem b).gamma a = a.1 :=
  inverseOpHom_primitiveStabilizerHom b a

end Family

end ModularRep.PaperProofs.TypeBExceptionalPrimitiveFamilySplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
