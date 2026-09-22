import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

/-!
# Sparse polynomial identities yield inverse and rank certificates

The arrays and annihilator witnesses are explicit arithmetic data.
Their polynomial identities must be proved from the literal payload.
Evaluation uses the target root of the original iota.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSparseRowInverseCertificate

open ModularRep
open SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

universe u v w x y z

structure SparseRowInverseCertificate
    (N : ℕ) (Row : Type u) (Column : Type v) (Index : Type w) (n : ℕ) where
  rows : Row → Column → Scalar N
  basisPosition : Fin n → Row
  pivotColumn : Fin n → Column
  inverse : Fin n → Fin n → Scalar N
  coefficients : Row → Fin n → Scalar N
  inverseAnnihilator : Fin n → Fin n → AnnihilatorData N Index
  reconstructionAnnihilator : Row → Column → AnnihilatorData N Index

namespace SparseRowInverseCertificate

variable {N n : ℕ} {Row : Type u} {Column : Type v} {Index : Type w}
variable (D : SparseRowInverseCertificate N Row Column Index n)

def inverseResidual (a b : Fin n) : ℚ[X] :=
  (∑ j : Fin n,
    (D.rows (D.basisPosition a) (D.pivotColumn j)).toPolynomial *
      (D.inverse j b).toPolynomial) - (if a = b then 1 else 0)

def reconstructionResidual (r : Row) (c : Column) : ℚ[X] :=
  (D.rows r c).toPolynomial -
    ∑ a : Fin n, (D.coefficients r a).toPolynomial *
      (D.rows (D.basisPosition a) c).toPolynomial

variable [Fintype Index]

def InverseIdentities : Prop :=
  ∀ a b, D.inverseResidual a b = (D.inverseAnnihilator a b).combination

def ReconstructionIdentities : Prop :=
  ∀ r c, D.reconstructionResidual r c = (D.reconstructionAnnihilator r c).combination

section Evaluation

variable {K : Type x} [Field K] [CharZero K]

def evaluatedRows (zeta : K) : Row → Column → K := fun r c => (D.rows r c).eval zeta

theorem evaluated_right_inverse
    {zeta : K} (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N)
    (hInverse : D.InverseIdentities) :
    Matrix.of (fun a c : Fin n =>
      D.evaluatedRows zeta (D.basisPosition a) (D.pivotColumn c)) *
        Matrix.of (fun a b : Fin n => (D.inverse a b).eval zeta) = 1 := by
  ext a b
  have h := (D.inverseAnnihilator a b).ratEval_eq_of_sub_identity hN hzeta
    (∑ j : Fin n,
      (D.rows (D.basisPosition a) (D.pivotColumn j)).toPolynomial *
        (D.inverse j b).toPolynomial)
    (if a = b then (1 : ℚ[X]) else 0) (hInverse a b)
  simpa only [evaluatedRows, Matrix.mul_apply, Matrix.of_apply,
    Matrix.one_apply, map_sum, map_mul, ratEval_scalar,
    apply_ite, map_one, map_zero] using h

theorem evaluated_reconstruct
    {zeta : K} (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N)
    (hReconstruction : D.ReconstructionIdentities) (r : Row) :
    D.evaluatedRows zeta r =
      ∑ a : Fin n, (D.coefficients r a).eval zeta •
        D.evaluatedRows zeta (D.basisPosition a) := by
  funext c
  have h := (D.reconstructionAnnihilator r c).ratEval_eq_of_sub_identity hN hzeta
    (D.rows r c).toPolynomial
    (∑ a : Fin n, (D.coefficients r a).toPolynomial *
      (D.rows (D.basisPosition a) c).toPolynomial) (hReconstruction r c)
  simpa only [evaluatedRows, map_sum, map_mul, ratEval_scalar,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

def rowInverseCertificate
    {zeta : K} (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N)
    (hInverse : D.InverseIdentities) (hReconstruction : D.ReconstructionIdentities) :
    RowInverseCertificate K (D.evaluatedRows zeta) n where
  basisPosition := D.basisPosition
  pivotColumn := D.pivotColumn
  inverse := Matrix.of (fun a b => (D.inverse a b).eval zeta)
  right_inverse := D.evaluated_right_inverse hN hzeta hInverse
  coefficients := fun r a => (D.coefficients r a).eval zeta
  reconstruct := D.evaluated_reconstruct hN hzeta hReconstruction

end Evaluation

section SameIota

variable {p : ℕ} {k : Type y} {K : Type x} {X : Type z}
variable [Field k] [Field K] [CharZero K] [Group X] [Finite X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : SameIotaConductorRoot iota N)

def sameIotaRowInverseCertificate
    (hInverse : D.InverseIdentities) (hReconstruction : D.ReconstructionIdentities) :
    RowInverseCertificate K (D.evaluatedRows (targetRoot iota R)) n :=
  D.rowInverseCertificate R.conductor_pos (targetRoot_isPrimitive iota R)
    hInverse hReconstruction

def sameIotaRankCertificate
    (hInverse : D.InverseIdentities) (hReconstruction : D.ReconstructionIdentities) :
    FiniteRowRankCertificate K (D.evaluatedRows (targetRoot iota R)) n :=
  rankCertificate (D.sameIotaRowInverseCertificate iota R hInverse hReconstruction)

theorem sameIota_rows_finrank
    (hInverse : D.InverseIdentities) (hReconstruction : D.ReconstructionIdentities) :
    Module.finrank K
      (Submodule.span K (Set.range (D.evaluatedRows (targetRoot iota R)))) = n :=
  (D.sameIotaRankCertificate iota R hInverse hReconstruction).rows_finrank

end SameIota
end SparseRowInverseCertificate
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSparseRowInverseCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
