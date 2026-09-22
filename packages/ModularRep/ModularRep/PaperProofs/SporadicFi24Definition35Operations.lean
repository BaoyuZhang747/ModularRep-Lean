import ModularRep.PaperProofs.EvenFieldFLZSourceConditions
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Literal Fischer Definition 3.5 problem

This module identifies the ambient block data in a Definition 3.5 problem
with the operations catalogue of a literal Fischer carrier. It constructs no
block-preserving character-weight equivalence, block-induction conclusion,
Definition 3.5 witness, BAW-goodness assertion, or iBAW conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24Definition35Operations

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {p : ℕ} {k K X Gamma : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable [Group Gamma] [Finite Gamma]

/-- The literal Fischer carrier supplies the operations-level Brauer support
required by `Definition35Problem.ofOperations`. -/
theorem literalOperationsBrauerSupport
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X)) :
    OperationsBrauerSupport iota hinj R.1.operations := by
  simpa only [OperationsBrauerSupport] using
    (operationsBrauerSupport (iota := iota) (hinj := hinj) R)

/-- Minimal Definition 3.5 problem on the literal Fischer set of blocks. -/
def literalDefinition35Problem
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X))
    (block : ActualBlock (k := k) (X := X))
    (gamma : Gamma →* MulAut X)
    (gammaBlock_fixed : ∀ a : Gamma,
      inverseOpHom gamma a • block = block)
    (localReduction : ∀ w : LiteralWeightFibre R.1 block,
      SelectedLocalReductionSource R.1 block w) :
    Definition35Problem :=
  Definition35Problem.ofOperations
    iota hinj R.1 block gamma gammaBlock_fixed
      (literalOperationsBrauerSupport iota hinj R) localReduction

end ModularRep.PaperProofs.SporadicFi24Definition35Operations


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
