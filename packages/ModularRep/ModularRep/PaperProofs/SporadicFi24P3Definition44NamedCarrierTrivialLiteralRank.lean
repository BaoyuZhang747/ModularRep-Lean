import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCompleteIntegerChecks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDuplicateColumnSymmetrization
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

/-! Literal full trivial-sector rows and their original-permutation symmetrization. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLiteralRank

open ModularRep
open SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open SporadicFi24P3Definition44NamedCarrierTrivialIntegerEvaluation
open SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialRootEvaluation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierTrivialCompleteIntegerChecks
open SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierDuplicateColumnSymmetrization
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

universe u v w
variable {K : Type u} [Field K] [CharZero K]

def checkedRepresentativeRowInverseCertificate
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 10015005) :
    RowInverseCertificate K (evaluatedRows (localRoots zeta)) 41 :=
  representativeRowInverseCertificate (localRoots zeta) (local_modulus_zero hzeta)
    inverseChecks constantChecks reconstructionChecks

def checkedRawRowInverseCertificate
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 10015005) :
    RowInverseCertificate K (rawEvaluatedRows zeta) 41 := by
  rw [rawEvaluatedRows_eq_expansion zeta columnChecks]
  exact expandedRowInverseCertificate (fun c => some (columnLabel c, (1 : K)))
    pivotColumn (by intro j; rw [columnLabel_pivot])
    (checkedRepresentativeRowInverseCertificate zeta hzeta)

def checkedRawRankCertificate
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 10015005) :
    FiniteRowRankCertificate K (rawEvaluatedRows zeta) 41 :=
  rankCertificate (checkedRawRowInverseCertificate zeta hzeta)

theorem literal_rows_finrank
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 10015005) :
    Module.finrank K (Submodule.span K (Set.range (rawEvaluatedRows zeta))) = 41 :=
  (checkedRawRankCertificate zeta hzeta).rows_finrank

theorem literal_plus_rows_finrank
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 10015005) :
    Module.finrank K (Submodule.span K
      (Set.range fun r c => rawEvaluatedRows zeta r c + rawEvaluatedRows zeta r (fullPerm c))) = 36 :=
  symmetrizedRows_finrank_of_duplicate_columns (rawEvaluatedRows zeta)
    (checkedRawRankCertificate zeta hzeta) columnLabel pivotColumn columnLabel_pivot
    (rawEvaluatedRows_duplicate zeta columnChecks) fullPerm sigma routing_intertwines_perm
    sigma_involutive representativeColumn_function_fixed_card

variable {p : ℕ} {k : Type v} {X : Type w}
variable [Field k] [Group X] [Finite X]

def sameIotaLiteralRankCertificate
    (iota : PrimeRegularRootEmbedding p k K X)
    (roots : SameIotaConductorRoot iota 10015005) :
    FiniteRowRankCertificate K (rawEvaluatedRows (targetRoot iota roots)) 41 :=
  checkedRawRankCertificate (targetRoot iota roots) (targetRoot_isPrimitive iota roots)

theorem sameIota_literal_rows_finrank
    (iota : PrimeRegularRootEmbedding p k K X)
    (roots : SameIotaConductorRoot iota 10015005) :
    Module.finrank K
      (Submodule.span K (Set.range (rawEvaluatedRows (iota.lift roots.source_root)))) = 41 := by
  rw [← targetRoot_eq_iota_lift_source iota roots]
  exact (sameIotaLiteralRankCertificate iota roots).rows_finrank

theorem sameIota_literal_plus_rows_finrank
    (iota : PrimeRegularRootEmbedding p k K X)
    (roots : SameIotaConductorRoot iota 10015005) :
    Module.finrank K (Submodule.span K
      (Set.range fun r c => rawEvaluatedRows (iota.lift roots.source_root) r c +
        rawEvaluatedRows (iota.lift roots.source_root) r (fullPerm c))) = 36 := by
  rw [← targetRoot_eq_iota_lift_source iota roots]
  exact literal_plus_rows_finrank (targetRoot iota roots) (targetRoot_isPrimitive iota roots)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLiteralRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
