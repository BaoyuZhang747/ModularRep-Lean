import ModularRep.PaperProofs.TypeBFLZSymbolCarriers

/-!
# Terminal core removal on literal odd-defect symbols

The carrier is the actual finite-row quotient from the symbol module.
Odd defect excludes the associated-copy ambiguity of degenerate symbols.
The positive hook length and hook/cohook mode are explicit. Only the
standard terminal-removal existence/uniqueness theorem is a source input;
the core operator, its specification and idempotence are deductions.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZSymbolCores

open TypeBFLZSymbolCarriers

/-- The target is an actual odd-defect symbol reached by the specified
literal hook/cohook steps, terminal among all actual symbols. -/
def TerminalCore (kind : RemovalKind) (e : ℕ) (mu kappa : OddSymbol) : Prop :=
  RemovesStar kind e mu.val kappa.val ∧ Terminal kind e kappa.val

theorem terminalCore_self {kind : RemovalKind} {e : ℕ} {kappa : OddSymbol}
    (h : Terminal kind e kappa.val) : TerminalCore kind e kappa kappa :=
  ⟨Relation.ReflTransGen.refl, h⟩

/-- E1: exact terminal-removal existence/uniqueness on the literal quotient
and odd-defect carrier. This contains no chosen map, arbitrary symbol type,
character/block data, or manuscript target. The intended published scope
is Fong-Srinivasan/Olsson with the explicit hook/cohook convention. -/
structure CoreRemovalCertificate (kind : RemovalKind) (e : ℕ) where
  positive : 0 < e
  terminal_unique : ∀ mu : OddSymbol, ∃! kappa : OddSymbol, TerminalCore kind e mu kappa

variable {kind : RemovalKind} {e : ℕ} (source : CoreRemovalCertificate kind e)

/-- Choose the uniquely determined terminal actual odd-defect symbol. -/
def takeCore (mu : OddSymbol) : OddSymbol :=
  Classical.choose (source.terminal_unique mu).exists

theorem takeCore_spec (mu : OddSymbol) : TerminalCore kind e mu (takeCore source mu) :=
  Classical.choose_spec (source.terminal_unique mu).exists

theorem takeCore_unique (mu kappa : OddSymbol) (h : TerminalCore kind e mu kappa) :
    takeCore source mu = kappa :=
  (source.terminal_unique mu).unique (takeCore_spec source mu) h

theorem takeCore_of_terminal (kappa : OddSymbol) (h : Terminal kind e kappa.val) :
    takeCore source kappa = kappa :=
  takeCore_unique source kappa kappa (terminalCore_self h)

theorem takeCore_idempotent (mu : OddSymbol) :
    takeCore source (takeCore source mu) = takeCore source mu :=
  takeCore_of_terminal source (takeCore source mu) (takeCore_spec source mu).2

/-- A finite initial sequence of actual removals does not change the core. -/
theorem takeCore_eq_of_reachable (mu nu : OddSymbol)
    (h : RemovesStar kind e mu.val nu.val) :
    takeCore source mu = takeCore source nu :=
  takeCore_unique source mu (takeCore source nu)
    ⟨Relation.ReflTransGen.trans h (takeCore_spec source nu).1, (takeCore_spec source nu).2⟩

/-- The extracted core remains outside the equal-row degeneracy scope. -/
theorem takeCore_not_degenerate (mu : OddSymbol) :
    ¬ Degenerate (takeCore source mu).val :=
  odd_defect_not_degenerate (takeCore source mu).property

end ModularRep.PaperProofs.TypeBFLZSymbolCores


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
