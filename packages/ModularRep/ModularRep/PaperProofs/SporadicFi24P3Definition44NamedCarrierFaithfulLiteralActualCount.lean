import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorRankCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLiteralRank

/-! Actual same-iota faithful-sector count from the checked literal matrix and source dictionaries. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualSectorRankCertificate
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierFaithfulLiteralRank

universe u
variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem actualFaithfulSector_card_twentyFive_of_literal_values
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1})
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu.1 (Fin 74))
    (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
    (roots : SameIotaConductorRoot iota 770385)
    (hvalues : ∀ r c,
      (C.character r).1 (A.representative c).1 =
        rawEvaluatedRows (iota.lift roots.source_root) r c) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu.1} = 25 := by
  have hvalues' : ∀ r c,
      (C.character r).1 (A.representative c).1 =
        rawEvaluatedRows (targetRoot iota roots) r c := by
    intro r c
    rw [targetRoot_eq_iota_lift_source iota roots]
    exact hvalues r c
  exact actualSector_card_of_certificate iota hinj blocks D nu.1 C A
    (rawEvaluatedRows (targetRoot iota roots)) hvalues' 25
    (sameIotaLiteralRankCertificate iota roots)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
