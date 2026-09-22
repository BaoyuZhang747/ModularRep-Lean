import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
import ModularRep.PaperProofs.FiniteRowRankCertificate

/-!
# Actual sector cardinalities from finite row certificates

Actual ordinary decomposition and coverage identify the Brauer span.
Evaluation at actual regular representatives identifies its coordinates.
A nonzero minor and explicit reconstruction derive the matrix rank.
No cardinality, equivalence, span equality or rank assertion is a source.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorRankCertificate

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation

universe u v w

variable {p : ℕ} {k K X BlockIndex : Type u}
variable {Row : Type v} {Column : Type w}
variable [Field k] [Field K]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (nu : CentralSector (k := k) (X := X))
variable (C : ActualSectorOrdinaryRows iota hinj blocks D nu Row)
variable (A : PrimeRegularRepresentativeCover p X Column)
variable (matrix : Row → Column → K)
variable (hvalues : ∀ r c,
  (C.character r).1 (A.representative c).1 = matrix r c)

include D C A hvalues

theorem actualSectorOrdinarySpan_finrank_of_certificate
    (n : ℕ) (certificate : FiniteRowRankCertificate K matrix n) :
    Module.finrank K (actualSectorOrdinarySpan iota hinj blocks D nu C) = n := by
  calc
    Module.finrank K (actualSectorOrdinarySpan iota hinj blocks D nu C) =
        Module.finrank K (Submodule.span K (Set.range matrix)) :=
      (actualSectorEvaluationEquiv iota hinj blocks D nu C A matrix hvalues).finrank_eq
    _ = n := certificate.rows_finrank

theorem actualSector_card_of_certificate
    (n : ℕ) (certificate : FiniteRowRankCertificate K matrix n) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = n := by
  calc
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} =
        Module.finrank K (actualSectorOrdinarySpan iota hinj blocks D nu C) :=
      actualSector_card_eq_ordinarySpan_finrank iota hinj blocks D nu C
    _ = n := actualSectorOrdinarySpan_finrank_of_certificate
      iota hinj blocks D nu C A matrix hvalues n certificate

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorRankCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
