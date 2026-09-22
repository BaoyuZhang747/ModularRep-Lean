import ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
import ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate

/-!
# Ambient adapters for the centreless central character quotient

This module contains only the two adapters that specialise the independent
centreless quotient kernel to the sole ambient family in the Feng--Li--Zhang
Theorem 5.7 gate.  Keeping them here prevents the equation-(3.17) and
quotient-fibre route from importing that theorem gate.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- On the literal ambient family, the centreless source identification
discharges the central character kernel for every block and character. -/
theorem ambient_centralCharacterKernel_eq_bot
    {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (identification : CentrelessTypeCSourceIdentification
      scope coverage model frobenius)
    (block : (AmbientFamily scope coverage).Block)
    (psi : Definition35Brauer
      ((AmbientFamily scope coverage).problem block)) :
    centralCharacterKernel
      ((AmbientFamily scope coverage).problem block) psi = ⊥ :=
  centralCharacterKernel_eq_bot_of_centerless
    ((AmbientFamily scope coverage).problem block)
    identification.centerless psi

/-- Every central character quotient on the literal ambient family is
canonically the ambient family group itself. -/
def ambientCentralCharacterQuotientEquiv
    {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (identification : CentrelessTypeCSourceIdentification
      scope coverage model frobenius)
    (block : (AmbientFamily scope coverage).Block)
    (psi : Definition35Brauer
      ((AmbientFamily scope coverage).problem block)) :
    CentralCharacterQuotient
        ((AmbientFamily scope coverage).problem block) psi ≃*
      (AmbientFamily scope coverage).H :=
  centerlessCentralCharacterQuotientEquiv
    ((AmbientFamily scope coverage).problem block)
    identification.centerless psi

end ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
