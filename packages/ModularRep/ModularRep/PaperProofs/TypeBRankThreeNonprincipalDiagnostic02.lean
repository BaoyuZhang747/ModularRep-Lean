import ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication
import Lean

set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.proofs.threshold 1000000
set_option pp.maxSteps 1000000

run_cmd do
  let env ← Lean.getEnv
  let mut names := #[
    `ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication.ManuscriptReduction,
    `ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication.ManuscriptReduction.mk,
    `ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication.nonprincipal_rank_three_source_instantiated]
  let mut index := 0
  while index < names.size do
    let name := names[index]!
    let some info := env.find? name | throwError "Missing {name}"
    let mut references := info.type.getUsedConstants
    if let some body := info.value? (allowOpaque := true) then
      references := references ++ body.getUsedConstants
    if references.contains `sorryAx then
      Lean.logInfo m!"DIRECT_SORRY {name}"
      Lean.Elab.Command.elabCommand (← `(#print $(Lean.mkIdent name)))
    for referenced in references do
      if (referenced.toString.startsWith "ModularRep.PaperProofs.TypeBRankThreeNonprincipal" ||
          referenced.toString.startsWith "_private.ModularRep.PaperProofs.TypeBRankThreeNonprincipal") &&
          !names.contains referenced then
        names := names.push referenced
    index := index + 1
  Lean.logInfo m!"DIAGNOSTIC_VISITED {names.size}"


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
