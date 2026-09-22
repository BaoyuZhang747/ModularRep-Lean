import ModularRep.PaperProofs.TypeBQ3FaithfulCriterionAssembly
import ModularRep.PaperProofs.TypeBQ3AssemblyCriterionData

/-!
The faithful fixed-block clauses use the actual block stabilizer. Literal
support identifies an actor in that stabilizer whenever two supported
characters satisfy the intrinsic action equation. This converts the action
packaging while retaining the matching and every selected local clause.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyFaithfulNormalization

open ModularRep CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBExceptionalQ3Proposition416Actual TypeBQ3FaithfulFibreBinding
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalRadicalDecoding
open TypeBQ3FaithfulCriterionAssembly
open Formalisation.ComputationArithmetic

variable {k K X : Type} [Field k] [Field K] [CharZero K]
  [Group X] [Finite X] [CharP k 2] [IsAlgClosed k]

local instance groupFintype : Fintype X := Fintype.ofFinite X
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (root : PrimeRegularRootEmbedding 2 k K X)
  (hinj : IrreducibleBrauerCharacterInjectivity root)
  {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)
  (i : Q3Block)

include hinj

/-- A supported character-action equation determines literal block stability. -/
theorem block_fixed_of_supported_values
    (alpha : (MulAut X)ᵐᵒᵖ)
    (phi psi : BrauerFibre root (primitiveBlockOfLabel blocks i))
    (values : psi.val = alpha • phi.val) :
    alpha ∈ actualBlockStabilizer blocks i := by
  have hphi := (supported_iff_namedBlock root hinj blocks i phi.val).mp phi.property
  have hpsi := (supported_iff_namedBlock root hinj blocks i psi.val).mp psi.property
  have transported := primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
    root hinj blocks alpha phi.val
  rw [← values, hpsi, hphi] at transported
  exact transported.symm

/-- The existing named-fibre action has the prescribed underlying character. -/
theorem brauerStep_eq_of_values
    (alpha : actualBlockStabilizer blocks i)
    (phi psi : BrauerFibre root (primitiveBlockOfLabel blocks i))
    (values : psi.val = alpha.val • phi.val) :
    psi = brauerStep root hinj blocks i alpha phi := by
  apply Subtype.ext
  exact values.trans (brauerStep_val root hinj blocks i alpha phi).symm

variable (R : CoverWeightSource (k := k) (K := K) X)

/-- Normalize the intrinsic graph of the same complete faithful criterion. -/
theorem of_faithfulClauses
    (omega : BrauerFibre root (primitiveBlockOfLabel blocks i) ≃
      CoverWeight R (primitiveBlockOfLabel blocks i))
    (clauses : TypeBQ3FaithfulCriterionAssembly.CompleteClauses
      root hinj blocks i R omega) :
    TypeBQ3AssemblyCriterionData.CompleteClauses root R
      (primitiveBlockOfLabel blocks i) omega := by
  rcases clauses with ⟨graph, radical, partition, localEquiv, localClass,
    localCovariance, packets⟩
  refine ⟨?_, ?_, partition, localEquiv, localClass, ?_, packets⟩
  · intro alpha phi psi values
    let actor : actualBlockStabilizer blocks i :=
      ⟨alpha, block_fixed_of_supported_values root hinj blocks i alpha phi psi values⟩
    have step := brauerStep_eq_of_values root hinj blocks i actor phi psi values
    exact (congrArg (fun chi => (omega chi).val) step).trans (graph actor phi)
  · intro alpha phi psi values
    let actor : actualBlockStabilizer blocks i :=
      ⟨alpha, block_fixed_of_supported_values root hinj blocks i alpha phi psi values⟩
    have step := brauerStep_eq_of_values root hinj blocks i actor phi psi values
    exact (congrArg (part omega) step).trans (radical actor phi)
  · intro alpha Q phi psi values
    let actor : actualBlockStabilizer blocks i :=
      ⟨alpha, block_fixed_of_supported_values root hinj blocks i alpha
        phi.val psi.val values⟩
    exact localCovariance actor Q phi psi
      (brauerStep_eq_of_values root hinj blocks i actor phi.val psi.val values)

end ModularRep.PaperProofs.TypeBQ3AssemblyFaithfulNormalization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
