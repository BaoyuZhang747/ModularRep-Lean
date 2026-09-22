import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
import Mathlib.Logic.Equiv.Basic
import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation

open SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open SporadicFi24P3Definition44NamedCarrierTrivialColumnData

set_option maxRecDepth 32768

def sigmaIndex (j : Fin 41) : Fin 41 := columnLabel (fullIndex (pivotColumn j))

theorem columnLabel_pivot : ∀ j, columnLabel (pivotColumn j) = j := by decide

theorem fullIndex_involutive : Function.Involutive fullIndex := by
  change ∀ c, fullIndex (fullIndex c) = c
  decide

theorem sigmaIndex_involutive : Function.Involutive sigmaIndex := by
  change ∀ j, sigmaIndex (sigmaIndex j) = j
  decide

theorem routing_intertwines :
    ∀ c, columnLabel (fullIndex c) = sigmaIndex (columnLabel c) := by decide

def fullPerm : Equiv.Perm (Fin 91) :=
  Function.Involutive.toPerm fullIndex fullIndex_involutive

def sigma : Equiv.Perm (Fin 41) :=
  Function.Involutive.toPerm sigmaIndex sigmaIndex_involutive

theorem fullPerm_apply (c : Fin 91) : fullPerm c = fullIndex c := rfl

theorem sigma_apply (j : Fin 41) : sigma j = sigmaIndex j := rfl

theorem fullPerm_involutive : Function.Involutive fullPerm := fullIndex_involutive

theorem sigma_involutive : Function.Involutive sigma := sigmaIndex_involutive

theorem routing_intertwines_perm (c : Fin 91) :
    columnLabel (fullPerm c) = sigma (columnLabel c) := routing_intertwines c

theorem representativeColumn_fixed_card : Nat.card {j : Fin 41 // sigma j = j} = 31 := by
  change Nat.card {j : Fin 41 // sigmaIndex j = j} = 31
  rw [Nat.card_eq_fintype_card]
  decide

theorem representativeColumn_function_fixed_card :
    Nat.card (Function.fixedPoints sigma) = 31 := representativeColumn_fixed_card

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
