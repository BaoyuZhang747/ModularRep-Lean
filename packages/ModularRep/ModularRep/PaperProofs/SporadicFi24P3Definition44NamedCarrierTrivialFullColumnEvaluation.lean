import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRootEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation

open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open SporadicFi24P3Definition44NamedCarrierTrivialIntegerEvaluation
open SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialRootEvaluation
open SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion

variable {K : Type*} [Field K]

def ColumnChecks : Prop := ∀ r c, rawRow r c = row r (columnLabel c)

def rawEvaluatedRows (zeta : K) (r : Fin 108) (c : Fin 91) : K :=
  eval (localRoots zeta (columnTag (columnLabel c))) (rawRow r c)

theorem rawEvaluatedRows_eq_representative
    (zeta : K) (hColumn : ColumnChecks) (r : Fin 108) (c : Fin 91) :
    rawEvaluatedRows zeta r c = evaluatedRows (localRoots zeta) r (columnLabel c) := by
  unfold rawEvaluatedRows
  rw [hColumn r c]
  rfl

theorem rawEvaluatedRows_duplicate
    (zeta : K) (hColumn : ColumnChecks) (r : Fin 108) (c : Fin 91) :
    rawEvaluatedRows zeta r c = rawEvaluatedRows zeta r (pivotColumn (columnLabel c)) := by
  rw [rawEvaluatedRows_eq_representative zeta hColumn,
    rawEvaluatedRows_eq_representative zeta hColumn, columnLabel_pivot]

theorem rawEvaluatedRows_eq_expansion (zeta : K) (hColumn : ColumnChecks) :
    rawEvaluatedRows zeta = fun r =>
      columnExpansion (fun c => some (columnLabel c, (1 : K)))
        (evaluatedRows (localRoots zeta) r) := by
  funext r c
  rw [rawEvaluatedRows_eq_representative zeta hColumn]
  change evaluatedRows (localRoots zeta) r (columnLabel c) =
    (1 : K) * evaluatedRows (localRoots zeta) r (columnLabel c)
  rw [one_mul]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
