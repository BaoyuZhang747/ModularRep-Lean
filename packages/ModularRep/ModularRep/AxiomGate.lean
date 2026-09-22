import Lean

/-!
# Kernel axiom gate

This module provides the mechanical axiom check used by the two policy
files.  It deliberately answers only whether a declaration depends on a
nonstandard axiom.  It cannot determine whether a theorem parameter is an
independent source-shaped input or a restatement of the desired conclusion.
-/

open Lean Meta Elab Command

/-- Fail unless a declaration uses only propositional extensionality,
classical choice, and quotient soundness. -/
elab "assert_only_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed : Lean.NameSet :=
    Lean.NameSet.ofList [``propext, ``Classical.choice, ``Quot.sound]
  let mut forbidden : Array Name := #[]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      forbidden := forbidden.push axiomName
  unless forbidden.isEmpty do
    throwError "{n} depends on forbidden axioms: {forbidden}"

/-- Reject the simplest form of conclusion smuggling: a theorem whose local
hypotheses contain a proposition definitionally equal to its final
conclusion.  This is only a necessary check.  It cannot detect a logically
equivalent hypothesis, a conclusion hidden in a structure field, or a family
of hypotheses that jointly imply the conclusion for circular reasons. -/
elab "assert_no_direct_conclusion_hypothesis " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  liftTermElabM do
    let info ← getConstInfo name
    forallTelescope info.type fun xs conclusion => do
      for x in xs do
        let hypothesisType ← inferType x
        if ← isDefEq hypothesisType conclusion then
          throwError
            "{n} has a hypothesis definitionally equal to its conclusion: {hypothesisType}"


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
