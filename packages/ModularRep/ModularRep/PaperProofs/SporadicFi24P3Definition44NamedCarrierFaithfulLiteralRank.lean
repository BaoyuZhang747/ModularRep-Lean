import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCompleteIntegerChecks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCompleteColumnChecks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

/-! The literal 74-by-91 faithful-sector matrix has rank 25 at the retained root. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLiteralRank

open ModularRep
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerEvaluation
open SporadicFi24P3Definition44NamedCarrierFaithfulRootEvaluation
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierFaithfulCompleteIntegerChecks
open SporadicFi24P3Definition44NamedCarrierFaithfulCompleteColumnChecks
open SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

universe u v w
variable {K : Type u} [Field K] [CharZero K]

def checkedRepresentativeRowInverseCertificate
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 770385) :
    RowInverseCertificate K (evaluatedRows (localRoots zeta)) 25 :=
  representativeRowInverseCertificate (localRoots zeta) (local_modulus_zero hzeta)
    inverseChecks constantChecks reconstructionChecks

def checkedRawRowInverseCertificate
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 770385) :
    RowInverseCertificate K (rawEvaluatedRows zeta) 25 := by
  have hrows : rawEvaluatedRows zeta =
      fun r => columnExpansion (evaluatedDescriptor zeta)
        (evaluatedRows (localRoots zeta) r) :=
    funext (rawEvaluatedRows_eq_expansion hzeta columnChecks)
  rw [hrows]
  exact expandedRowInverseCertificate (evaluatedDescriptor zeta) pivotColumn
    (evaluatedDescriptor_pivot zeta)
    (checkedRepresentativeRowInverseCertificate zeta hzeta)

def checkedRawRankCertificate
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 770385) :
    FiniteRowRankCertificate K (rawEvaluatedRows zeta) 25 :=
  rankCertificate (checkedRawRowInverseCertificate zeta hzeta)

theorem literal_rows_finrank
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 770385) :
    Module.finrank K (Submodule.span K (Set.range (rawEvaluatedRows zeta))) = 25 :=
  (checkedRawRankCertificate zeta hzeta).rows_finrank

variable {p : ℕ} {k : Type v} {X : Type w}
variable [Field k] [Group X] [Finite X]

def sameIotaLiteralRankCertificate
    (iota : PrimeRegularRootEmbedding p k K X)
    (roots : SameIotaConductorRoot iota 770385) :
    FiniteRowRankCertificate K (rawEvaluatedRows (targetRoot iota roots)) 25 :=
  checkedRawRankCertificate (targetRoot iota roots) (targetRoot_isPrimitive iota roots)

theorem sameIota_literal_rows_finrank
    (iota : PrimeRegularRootEmbedding p k K X)
    (roots : SameIotaConductorRoot iota 770385) :
    Module.finrank K
      (Submodule.span K (Set.range (rawEvaluatedRows (iota.lift roots.source_root)))) = 25 := by
  rw [← targetRoot_eq_iota_lift_source iota roots]
  exact (sameIotaLiteralRankCertificate iota roots).rows_finrank

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLiteralRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
