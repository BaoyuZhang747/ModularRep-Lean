import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierWeightSectorFinite
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorTwoBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedBlockSector
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv

/-!
# All original characteristic-two block counts from the sector data

Both residuals are derived inside the constructor. The centre action
forces every fixed block into the trivial sector, so faithful fixed
counts are unnecessary. The specified dictionaries remain explicit.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorCorrespondence

open ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorTwoBlocks
open SporadicFi24P3Definition44NamedCarrierFixedBlockSector
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {I : Type u} [Fintype I] {e : I → k[X]} (blocks : BlockIdempotentDecomposition e)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))

theorem exists_actual_equivariant_of_five_and_two_block_data
    (tau : MulAut X) (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hcardCenter : Nat.card (Subgroup.center X) = 3)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (trivialRoles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
    (faithfulRoles : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
    (hBr41 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1} = 41)
    (hBr31 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1 ∧
      MulOpposite.op tau • phi = phi} = 31)
    (hWt41 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = 1} = 41)
    (hWt31 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = 1 ∧ MulOpposite.op tau • w = w} = 31)
    (hBrOther : ∀ j : Fin 4,
      actualBrauerSignature iota hinj blocks tau (trivialRoles j.succ).1 = nonprincipalSignature j)
    (hWtOther : ∀ j : Fin 4,
      actualWeightSignature R tau (trivialRoles j.succ).1 = nonprincipalSignature j)
    (hBr25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = 25)
    (hWt25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // weightSector (R := R) w = nu} = 25)
    (hBrSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (faithfulRoles nu hnu 1).1} = 2)
    (hWtSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
        R.1.weightBlock w = (faithfulRoles nu hnu 1).1} = 2) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 2) (K := K) (X := X),
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) := by
  let _ := SporadicFi24P3Definition44NamedCarrierWeightSectorFinite.weight_finite_of_sector_counts
    R hWt41 hWt25
  have counts := SporadicFi24P3Definition44NamedCarrierActualTwoSectorCounts.actualBlockC2Counts_of_five_and_two_block_data
    iota hinj blocks R tau hcardCenter hinverts trivialRoles faithfulRoles
    hBr41 hBr31 hWt41 hWt31 hBrOther hWtOther hBr25 hWt25 hBrSmall hWtSmall
  exact exists_actual_equivariant_of_counts iota hinj R tau decomposition counts

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
