import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo

/-!
# The original correspondence from actual local ordinary tables

Both source records contain lower ordinary, radical, root and table data.
The three global weight-sector counts are derived inside the constructor.
One shared compatibility proof connects both tables to the original R.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicProposition57ComputationRelative
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierFaithfulLocalTableAtTwo
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorCorrespondence

universe u v w
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFintype : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

structure TrivialOrdinaryTableData
    (iota : PrimeRegularRootEmbedding 2 k K X) (tau : MulAut X)
    (Row : Fin 34 → Type v) (BlockD : Type u)
    [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD] where
  primeToCenter : ¬ 2 ∣ Nat.card (Subgroup.center X)
  catalogue : Catalogue 2 K (X ⧸ Subgroup.center X) (Fin 34) Row
  operationsD : LocalBlockInductionOperations
    (p := 2) (k := k) (K := K) (G := X ⧸ Subgroup.center X) (Block := BlockD)
  reductionU : ∀ i (theta : LocalDefectZeroCharacter (K := K)
      (liftedRepresentative iota (Subgroup.center X) le_rfl primeToCenter catalogue i)),
    CanonicalRawReduction iota (characterWeightAt iota.prime
      (liftedRepresentative iota (Subgroup.center X) le_rfl primeToCenter catalogue i) theta)
  reductionD : ∀ i (eta : LocalDefectZeroCharacter (K := K) (catalogue.representative i)),
    CanonicalRawReduction (quotientRoot iota (Subgroup.center X))
      (characterWeightAt iota.prime (catalogue.representative i) eta)
  compatibilityD : CanonicalLocalBlockCompatibility (quotientRoot iota (Subgroup.center X)) operationsD
  primitiveGlobal : CentralPrimeToPrimitiveImageSource (k := k)
    (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective (Subgroup.center X)) iota.prime
    (by simp only [QuotientGroup.ker_mk']; exact le_rfl)
    (by simpa only [QuotientGroup.ker_mk'] using primeToCenter)
  primitiveLocal : ∀ i, CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' (Subgroup.center X))
      (liftedRepresentative iota (Subgroup.center X) le_rfl primeToCenter catalogue i).1)
    (fixedNormalizer_surjective iota.prime (Subgroup.center X) le_rfl primeToCenter
      (liftedRepresentative iota (Subgroup.center X) le_rfl primeToCenter catalogue i).1
      (liftedRepresentative iota (Subgroup.center X) le_rfl primeToCenter catalogue i).2) iota.prime
    (fixedNormalizer_kernel_central (Subgroup.center X)
      (liftedRepresentative iota (Subgroup.center X) le_rfl primeToCenter catalogue i).1 le_rfl)
    (fixedNormalizer_kernel_primeTo (Subgroup.center X)
      (liftedRepresentative iota (Subgroup.center X) le_rfl primeToCenter catalogue i).1
      le_rfl primeToCenter)
  quotientAut : MulAut (X ⧸ Subgroup.center X)
  square : ∀ x : X, QuotientGroup.mk' (Subgroup.center X) (tau x) =
    quotientAut (QuotientGroup.mk' (Subgroup.center X) x)
  classesFixed : ∀ i : Fin 34, MulOpposite.op quotientAut •
    (Quotient.mk'' (catalogue.representative i) :
      RadicalConjugacyClass (p := 2) (G := X ⧸ Subgroup.center X)) =
        Quotient.mk'' (catalogue.representative i)
  entry : Fin 34 → TableSignatureEntry
  table : (List.ofFn entry).Perm correctedFi24Table8AtTwo
  total : ∀ i : Fin 34,
    Nat.card (LocalDefectZeroCharacter (K := K) (catalogue.representative i)) = (entry i).total
  fixed : ∀ j : catalogue.FixedIndex quotientAut,
    Nat.card (ActualFixedLocal catalogue quotientAut j) = (entry j.1).fixed

structure FaithfulOrdinaryTableData
    (iota : PrimeRegularRootEmbedding 2 k K X) (Row : Fin 34 → Type w) where
  nu0 : CentralSector (k := k) (X := X)
  nontrivial : nu0 ≠ 1
  catalogue : SectorCatalogue iota nu0 (Fin 34) Row
  reduction : ∀ i (theta : LocalDefectZeroCharacter (K := K) (catalogue.representative i)),
    CanonicalRawReduction iota (characterWeightAt iota.prime (catalogue.representative i) theta)
  table : (List.ofFn (fun i : Fin 34 =>
    Nat.card (RootSectorLocal iota nu0 (catalogue.representative i)))).Perm
      correctedFi24FaithfulTable8AtTwo

variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {BIndex : Type u} [Fintype BIndex] {e : BIndex → k[X]}
variable (blocks : BlockIdempotentDecomposition e)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable {RowT : Fin 34 → Type v} {RowF : Fin 34 → Type w}
variable [∀ i, Finite (RowT i)] [∀ i, Finite (RowF i)]
variable {BlockD : Type u}
variable [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]

theorem exists_actual_equivariant_of_ordinary_tables
    (tau : MulAut X)
    (T : TrivialOrdinaryTableData iota tau RowT BlockD)
    (F : FaithfulOrdinaryTableData iota RowF)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hcardCenter : Nat.card (Subgroup.center X) = 3)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (trivialRoles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
    (faithfulRoles : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
    (hBr41 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1} = 41)
    (hBr31 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1 ∧
      MulOpposite.op tau • phi = phi} = 31)
    (hBrOther : ∀ j : Fin 4,
      actualBrauerSignature iota hinj blocks tau (trivialRoles j.succ).1 = nonprincipalSignature j)
    (hWtOther : ∀ j : Fin 4,
      actualWeightSignature R tau (trivialRoles j.succ).1 = nonprincipalSignature j)
    (hBr25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = 25)
    (hBrSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi =
        (faithfulRoles nu hnu 1).1} = 2)
    (hWtSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      Nat.card {weight : WeightClass (p := 2) (K := K) (X := X) //
        R.1.weightBlock weight = (faithfulRoles nu hnu 1).1} = 2) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 2) (K := K) (X := X),
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) := by
  have hWtTrivial := actualTrivialSectorCounts_of_table8
    (R := R) (iota := iota) (hprimeTo := T.primeToCenter)
    (C := T.catalogue) (OD := T.operationsD) (CU := T.reductionU) (CD := T.reductionD)
    (compatU := compatibility) (compatD := T.compatibilityD)
    (Sglobal := T.primitiveGlobal) (Slocal := T.primitiveLocal)
    (tau := tau) (tauD := T.quotientAut) (square := T.square)
    T.classesFixed T.entry T.table T.total T.fixed
  have hWtFaithful := allFaithfulSectorCounts_of_table8
    (iota := iota) (R := R) (nu0 := F.nu0) (C := F.catalogue)
    (CU := F.reduction) (compatibility := compatibility)
    tau hinverts hcardCenter F.nontrivial F.table
  exact exists_actual_equivariant_of_five_and_two_block_data
    iota hinj blocks R tau decomposition hcardCenter hinverts trivialRoles faithfulRoles
    hBr41 hBr31 hWtTrivial.1 hWtTrivial.2 hBrOther hWtOther hBr25 hWtFaithful hBrSmall hWtSmall

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
