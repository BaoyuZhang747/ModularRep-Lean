import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck

def sum : List ZPoly → ZPoly
  | [] => []
  | p :: ps => add p (sum ps)

def sumFin {n : ℕ} (p : Fin n → ZPoly) : ZPoly := sum (List.ofFn p)

section Evaluation
variable {K : Type*} [CommRing K]

theorem eval_sum (x : K) (ps : List ZPoly) :
    eval x (sum ps) = (ps.map (eval x)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [sum, eval_add, ih, List.map_cons, List.sum_cons]

theorem eval_sumFin (x : K) {n : ℕ} (p : Fin n → ZPoly) :
    eval x (sumFin p) = ∑ j, eval x (p j) := by
  simp [sumFin, eval_sum, List.map_ofFn, List.sum_ofFn]

end Evaluation
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
