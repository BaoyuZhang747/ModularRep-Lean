import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual

/-! A block with trivial maximal Brauer support forces the ambient p-core
to be trivial. This derives the radical condition needed for every weight
at the trivial subgroup from one retained specified defect-zero block. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRadicalOfDefectZero

open ModularRep
open SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment
open SporadicCompleteCollapseLemma52Actual (TrivialWeightSource)

variable {p : ℕ} {k G Block : Type*}
variable [Field k] [CharP k p] [Fact p.Prime] [Group G] [Finite G] [Fintype Block]
variable {e : Block → k[G]} (blocks : BlockIdempotentDecomposition e) (b : Block)
variable (hDefect : IsMaximalCentralBrauerDefect (p := p) blocks b (⊥ : Subgroup G))

include hDefect in
theorem pCore_eq_bot_of_defect_bot : pCore p G = ⊥ :=
  (hDefect.eq_of_nonzero_le (pCore p G) (pCore_isPGroup p G)
    (normal_pSubgroup_hasNonzeroCentralBrauerRestriction blocks b
      (pCore p G) (pCore_isPGroup p G)) bot_le).symm

include hDefect in
theorem bot_radical_of_defect_bot : IsRadicalSubgroup p (⊥ : Subgroup G) :=
  bot_isRadicalSubgroup_of_pCore_eq_bot (pCore_eq_bot_of_defect_bot blocks b hDefect)

include hDefect in
theorem trivialWeightSourceOfDefectBot : TrivialWeightSource (p := p) (X := G) :=
  ⟨Fact.out, bot_radical_of_defect_bot blocks b hDefect⟩

theorem trivialWeightSource_unique
    {p : ℕ} {G : Type*} [Group G]
    (T U : TrivialWeightSource (p := p) (X := G)) : T = U := by
  cases T
  cases U
  rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRadicalOfDefectZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
