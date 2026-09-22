import ModularRep.PaperProofs.TypeBFullBlockCondition
import ModularRep.PaperProofs.TypeBExceptionalOddPrimeOrder

/-!
# The exact one-way cyclic-defect source and exceptional application

Koshitani--Spath, J. Group Theory 19 (2016), 777--813, Theorem 1.1,
p. 778, applies to cyclic-defect blocks of the universal prime-to-ell
cover. We use its odd-prime specialization (both displayed primes are ell).
Its Lemma 3.3, p. 783, gives the global Spath formulation from block
witnesses; Spath, J. Group Theory 16 (2013), 159--220, Definition 4.1,
p. 182, fixes the full radical, central character and normalization clauses.

The independent generic domain below requires EVERY actual ell-subgroup
of the exact cover to be cyclic. Hence every block defect group is cyclic;
no caller-supplied defect-group assignment or block-result predicate is
needed. The output is the fixed complete family computed from the same
primitive blocks and guarded local root data. The universal certificate is
E2/U and is not inhabited here. Standard defect-group, quotient-fibre and
fixed-modular-system identifications remain E1/U as in the full output.

The exceptional wrapper contributes the manuscript's elementary deduction
in K: actual quotient divisibility and the order of this SAME full cover
give cyclicity of every ell-subgroup. It applies the generic certificate
only afterwards. It cannot silently substitute Spin or a threefold cover
for the exact cover of Omega_7(3).
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCyclicDefectSource

open ModularRep FDRepSimpleClassKZero
open EvenFieldFLZSourceConditions
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition

/-- General exact one-way source, independent of Type B. Neither its family
nor its result can be selected separately from the literal input data. -/
structure CyclicDefectCertificate : Prop where
  allBlocks : ∀ {ell : ℕ} {k K H : Type}
      [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
      [Group H] [Fintype H] [Fintype (LiteralPrimitiveBlock k H)]
      (prime : Nat.Prime ell) (odd : Odd ell)
      (iota : PrimeRegularRootEmbedding ell k K H)
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      (blocks : BlockIdempotentDecomposition
        (fun b : LiteralPrimitiveBlock k H => b.1))
      (localSource : PrimitiveLocalSource iota)
      (coefficient : SpathCoefficientField ell k prime)
      (cover : EllPrimeCoverSource ell H)
      (divides_simple_order : ell ∣ Nat.card cover.S)
      (cyclic : ∀ P : Subgroup H, IsPGroup ell P → IsCyclic P),
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource) cover)

section Apply

variable {ell : ℕ} {k K H : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Fintype (LiteralPrimitiveBlock k H)]
variable (prime : Nat.Prime ell) (odd : Odd ell)
variable (iota : PrimeRegularRootEmbedding ell k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k H => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField ell k prime)
variable (cover : EllPrimeCoverSource ell H)

/-- Apply the generic source after the actual subgroup cyclicity is known. -/
def witness (source : CyclicDefectCertificate)
    (divides_simple_order : ell ∣ Nat.card cover.S)
    (cyclic : ∀ P : Subgroup H, IsPGroup ell P → IsCyclic P) :
    FamilyWitness (primitiveFamily iota hinj blocks prime localSource) cover :=
  Classical.choice (source.allBlocks prime odd iota hinj blocks localSource
    coefficient cover divides_simple_order cyclic)

/-- The full conditional exceptional endpoint uses the exact universal
ell-prime cover, its actual Omega quotient and its fixed primitive blocks.
The only deep input is the GENERAL cyclic-defect certificate above. -/
def exceptionalWitness (source : CyclicDefectCertificate)
    (N : TypeBCliffordCarriers.NormSource 3 (ZMod 3))
    (simpleQuotient : cover.S ≃* TypeBSpinCoverSource.Omega N)
    (nondefining : ell ≠ 3)
    (divides_omega : ell ∣ Nat.card (TypeBSpinCoverSource.Omega N))
    (cover_order : Nat.card H = TypeBExceptionalOddPrimeOrder.fullCoverOrder) :
    FamilyWitness (primitiveFamily iota hinj blocks prime localSource) cover := by
  have hSource : ell ∣ Nat.card cover.S := by
    rwa [Nat.card_congr simpleQuotient.toEquiv]
  exact witness prime odd iota hinj blocks localSource coefficient cover source hSource
    (TypeBExceptionalOddPrimeOrder.exceptionalCover_everyOddNondefiningSubgroupCyclic
      N prime odd nondefining cover simpleQuotient divides_omega cover_order)

end Apply

end ModularRep.PaperProofs.TypeBCyclicDefectSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
