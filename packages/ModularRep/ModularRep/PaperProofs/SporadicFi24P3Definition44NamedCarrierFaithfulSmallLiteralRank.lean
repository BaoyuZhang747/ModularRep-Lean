import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPolynomialRowInverseCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation

/-! Rank two for all 91 literal coordinates of the five faithful small-block rows. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallLiteralRank

open ModularRep
open SporadicFi24P3Definition44NamedCarrierPolynomialRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierFaithfulRootEvaluation

variable {K : Type*} [Field K] [CharZero K]

def faithfulSmallRowInverseCertificate (zeta : K) :
    RowInverseCertificate K
      (fun r : Fin 5 => rawEvaluatedRows zeta (faithfulSmallRow r)) 2 :=
  scaledPolynomialRowInverseCertificate
    (fun r c => rawRow (faithfulSmallRow r) c)
    (fun c => fullRoots zeta (fullTag c))
    smallBasis smallPivot smallMinor smallPivotChecks
    smallNumerator 3 (by decide) smallInverseChecks
    smallCoefficients smallReconstructionChecks

def faithfulSmallLiteralRankCertificate (zeta : K) :
    FiniteRowRankCertificate K
      (fun r : Fin 5 => rawEvaluatedRows zeta (faithfulSmallRow r)) 2 :=
  rankCertificate (faithfulSmallRowInverseCertificate zeta)

theorem faithful_small_literal_rows_finrank (zeta : K) :
    Module.finrank K (Submodule.span K
      (Set.range fun r : Fin 5 => rawEvaluatedRows zeta (faithfulSmallRow r))) = 2 :=
  (faithfulSmallLiteralRankCertificate zeta).rows_finrank

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallLiteralRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
