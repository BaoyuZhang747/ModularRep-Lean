import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinaryAllocation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockBrauerFixedRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralRank
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

/-! Actual remaining trivial-sector specified-block counts from full original ordinary values. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialActualCounts

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinaryAllocation
open SporadicFi24P3Definition44NamedCarrierActualBlockBrauerFixedRows
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralRank

universe u
variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (C : ActualSectorOrdinaryRows iota hinj blocks D
  (1 : CentralSector (k := k) (X := X)) (Fin 108))
variable (trivialRoles : Fin 5 ≃
  {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
variable (allocation : ∀ r, D.ordinaryBlock (C.character r) =
  (trivialRoles (printedBlockLabel r)).1)
variable (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
variable (roots : SameIotaConductorRoot iota 10015005)
variable (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
  rawEvaluatedRows (iota.lift roots.source_root) r c)

include allocation hvalues

theorem actualDihedralBlock_card_three_of_literal_values :
    Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (trivialRoles 2).1} = 3 := by
  have hcomplete := blockRows_complete_of_printed_allocation iota hinj blocks D C
    trivialRoles allocation 2 dihedralRow dihedral_fibre
  exact actualBlock_card_of_certificate iota hinj blocks D (trivialRoles 2).1
    (fun r => C.character (dihedralRow r)) hcomplete A
    (fun r : Fin 5 => rawEvaluatedRows (iota.lift roots.source_root) (dihedralRow r))
    (fun r c => hvalues (dihedralRow r) c) 3
    (dihedralLiteralRankCertificate (iota.lift roots.source_root))

theorem actualDihedralBlock_pointwise_fixed_of_literal_values
    (tau : MulAut X)
    (fusion : ∀ c : Fin 91, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (fullPerm c)).1 * x⁻¹) :
    ∀ phi : IBr iota, brauerBlock iota hinj blocks phi = (trivialRoles 2).1 →
      MulOpposite.op tau • phi = phi := by
  have hcomplete := blockRows_complete_of_printed_allocation iota hinj blocks D C
    trivialRoles allocation 2 dihedralRow dihedral_fibre
  have hmatrix : ∀ r : Fin 5, ∀ c : Fin 91,
      rawEvaluatedRows (iota.lift roots.source_root) (dihedralRow r) (fullPerm c) =
      rawEvaluatedRows (iota.lift roots.source_root) (dihedralRow r) c := by
    intro r c
    rw [dihedral_raw_eq_integer, dihedral_raw_eq_integer]
    exact dihedralIntegerRows_fixed r c
  exact actualBlockBrauer_fixed_of_ordinary_values iota hinj blocks (trivialRoles 2).1 tau
    D (fun r => C.character (dihedralRow r)) hcomplete A
    (fun r : Fin 5 => rawEvaluatedRows (iota.lift roots.source_root) (dihedralRow r))
    (fun r c => hvalues (dihedralRow r) c) fullPerm fusion hmatrix

theorem actualDihedralBlock_fixed_card_three_of_literal_values
    (tau : MulAut X)
    (fusion : ∀ c : Fin 91, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (fullPerm c)).1 * x⁻¹) :
    Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (trivialRoles 2).1 ∧
      MulOpposite.op tau • phi = phi} = 3 :=
  (actualBlock_fixed_card_eq_card_of_pointwise_fixed iota hinj blocks (trivialRoles 2).1 tau
    (actualDihedralBlock_pointwise_fixed_of_literal_values iota hinj blocks D C
      trivialRoles allocation A roots hvalues tau fusion)).trans
    (actualDihedralBlock_card_three_of_literal_values iota hinj blocks D C
      trivialRoles allocation A roots hvalues)

theorem actualZeroBlock_card_one_of_literal_values (j : Fin 2) :
    Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (trivialRoles (zeroRole j)).1} = 1 := by
  have hcomplete := blockRows_complete_of_printed_allocation iota hinj blocks D C
    trivialRoles allocation (zeroRole j) (zeroRow j) (zero_fibre j)
  exact actualBlock_card_of_certificate iota hinj blocks D (trivialRoles (zeroRole j)).1
    (fun r => C.character (zeroRow j r)) hcomplete A
    (zeroRows (iota.lift roots.source_root) j)
    (fun r c => hvalues (zeroRow j r) c) 1
    (zeroRankCertificate (iota.lift roots.source_root) j)

theorem actualZeroBlock_pointwise_fixed_of_literal_values (j : Fin 2)
    (tau : MulAut X)
    (fusion : ∀ c : Fin 91, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (fullPerm c)).1 * x⁻¹) :
    ∀ phi : IBr iota,
      brauerBlock iota hinj blocks phi = (trivialRoles (zeroRole j)).1 →
      MulOpposite.op tau • phi = phi := by
  have hcomplete := blockRows_complete_of_printed_allocation iota hinj blocks D C
    trivialRoles allocation (zeroRole j) (zeroRow j) (zero_fibre j)
  exact actualBlockBrauer_fixed_of_ordinary_values iota hinj blocks
    (trivialRoles (zeroRole j)).1 tau D (fun r => C.character (zeroRow j r)) hcomplete A
    (zeroRows (iota.lift roots.source_root) j)
    (fun r c => hvalues (zeroRow j r) c) fullPerm fusion
    (zeroRows_fixed (iota.lift roots.source_root) j)

theorem actualZeroBlock_fixed_card_one_of_literal_values (j : Fin 2)
    (tau : MulAut X)
    (fusion : ∀ c : Fin 91, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (fullPerm c)).1 * x⁻¹) :
    Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (trivialRoles (zeroRole j)).1 ∧
      MulOpposite.op tau • phi = phi} = 1 :=
  (actualBlock_fixed_card_eq_card_of_pointwise_fixed iota hinj blocks
    (trivialRoles (zeroRole j)).1 tau
    (actualZeroBlock_pointwise_fixed_of_literal_values iota hinj blocks D C
      trivialRoles allocation A roots hvalues j tau fusion)).trans
    (actualZeroBlock_card_one_of_literal_values iota hinj blocks D C
      trivialRoles allocation A roots hvalues j)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialActualCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
