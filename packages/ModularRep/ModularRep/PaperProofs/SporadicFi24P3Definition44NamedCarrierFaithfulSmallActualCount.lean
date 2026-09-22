import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulBlockOrdinaryAllocation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallLiteralRank
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

/-! Actual faithful small-block Brauer count from literal values and specified allocation. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierFaithfulBlockOrdinaryAllocation
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallLiteralRank
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

universe u
variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem actualFaithfulSmallBlock_card_two_of_literal_values
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1})
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu.1 (Fin 74))
    (roles : Fin 2 ≃
      {b : ActualBlock (k := k) (X := X) // blockSector b = nu.1})
    (allocation : ∀ r, D.ordinaryBlock (C.character r) =
      (roles (faithfulPrintedBlockLabel r)).1)
    (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
    (roots : SameIotaConductorRoot iota 770385)
    (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
      rawEvaluatedRows (iota.lift roots.source_root) r c) :
    Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (roles 1).1} = 2 := by
  have hcomplete := faithfulSmallRows_complete_of_allocation
    iota hinj blocks D nu C roles allocation
  exact actualBlock_card_of_certificate iota hinj blocks D (roles 1).1
    (fun r => C.character (faithfulSmallRow r)) hcomplete A
    (fun r : Fin 5 => rawEvaluatedRows (iota.lift roots.source_root) (faithfulSmallRow r))
    (fun r c => hvalues (faithfulSmallRow r) c) 2
    (faithfulSmallLiteralRankCertificate (iota.lift roots.source_root))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
