import ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers
import ModularRep.PaperProofs.TypeBGlobalExtensionBinding

/-!
# The four cyclic-extension clauses on the literal symplectic carriers

The existing generic extension constructor applies to the actual symplectic
subgroup of the conformal symplectic matrix group and its entrywise field
action. Its two cyclicity hypotheses come from the same structural source.
The two remaining inputs are the universal cyclic-extension principles over
the unchanged modular and ordinary coefficient fields.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddPrimeExtensionClauses

open ModularRep
open TypeBCriterionHypotheses
open TypeCOddPrimeConformalCriterionCarriers

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable [(SpSubgroup n F).Normal]
variable {ell : ℕ} {k K : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k]
variable [CharZero K] [IsAlgClosed K]

/-- All four actual extension clauses, including the two own-character
extensions on the actual local radical quotients, follow from the same
generic cyclic-extension construction. No final extension clause is a
source premise. -/
theorem extensionClauses
    (iota : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))
    (source : StructuralSource n F)
    (brauerPrinciple : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (ordinaryPrinciple : Representation.CyclicExtensionPrinciple.{0, 0, 0} K) :
    ExtensionClauses (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iota := by
  letI : IsCyclic (F ≃+* F) := source.field_cyclic
  exact TypeBGlobalExtensionBinding.extensionClauses
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iota
    brauerPrinciple ordinaryPrinciple source.quotient_cyclic

end ModularRep.PaperProofs.TypeCOddPrimeExtensionClauses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
