import ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily

/-!
# Canonical specified block families over finite splitting coefficients

The ordinary coefficient field has enough roots for the actual finite group.
Algebraic closure of that characteristic-zero field is not a hypothesis.
The constructor fixes actual primitive blocks, their canonical automorphism
stabilizers and the guarded common-root local block operations. It supplies
no matching or block-condition conclusion.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.CurrentFiniteSplittingFamily
open ModularRep Formalisation CharacterWeight FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37LiteralLocalExtension
universe u
section CanonicalPrimitiveFamily

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype (LiteralPrimitiveBlock k G)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G ↦ b.1))

/-- The specified local inputs for an arbitrary finite group in a splitting
ordinary coefficient field.  This replaces the unnecessary algebraic-closure
field in the older `PrimitiveLocalSource`, without modifying that source. -/
structure PrimitivePhysicalSource where
  ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G)
  blockSource : LocalBlockInductionSource
    (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G)
  idempotent : ∀ b : LiteralPrimitiveBlock k G,
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1
  blockCompatibility : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
    iota blockSource.operations
  reduction : ∀ (b : LiteralPrimitiveBlock k G) (w : LiteralWeightFibre blockSource b),
    SelectedLocalReductionSource blockSource b w
  reduction_roots : ∀ (b : LiteralPrimitiveBlock k G) (w : LiteralWeightFibre blockSource b),
    TypeBFixedRootDefinitionFamily.QuotientRootAgreement iota
      (SelectedRadical blockSource b w) (reduction b w).iota

/-- The canonical full primitive-block family.  Applied to `G/pCore`, this
is the specified quotient family required by a published quotient theorem. -/
def primitiveFamily (prime : p.Prime) (physical : PrimitivePhysicalSource iota) :
    Definition35Family p where
  ellPrime := prime
  k := k
  K := K
  H := G
  Block := LiteralPrimitiveBlock k G
  blockIdempotent b := b.1
  iota := iota
  irreducibleBrauerInjective := hinj
  blocks := blocks
  blockSource := physical.blockSource
  brauerBlock_transport := TypeBFixedRootDefinitionFamily.primitiveBrauerBlock_transport
    iota hinj blocks
  automorphisms := TypeBFixedRootDefinitionFamily.primitiveBlockAutomorphisms
  localReduction := physical.reduction

def primitiveFamily_automorphisms (prime : p.Prime) (physical : PrimitivePhysicalSource iota)
    (b : LiteralPrimitiveBlock k G) :
    Definition35AutomorphismStabilizerAdapter
      ((primitiveFamily iota hinj blocks prime physical).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (TypeBFixedRootDefinitionFamily.inverseOpHom_primitiveStabilizerHom b a).symm

end CanonicalPrimitiveFamily

end ModularRep.PaperProofs.CurrentFiniteSplittingFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
