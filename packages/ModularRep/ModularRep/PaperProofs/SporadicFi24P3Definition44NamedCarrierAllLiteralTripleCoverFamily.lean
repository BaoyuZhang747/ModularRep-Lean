import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllLiteralBrauerCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne

/-! The original full-cover Definition 4.1 family from checked literal Brauer values.
One internally constructed Omega indexes all packets and both Q=1 assertions. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllLiteralTripleCoverFamily

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts
open SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorCounts
open SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
open SporadicFi24P3Definition44NamedCarrierWeightSectorFinite
open SporadicFi24P3Definition44NamedCarrierAllPairs

open SporadicFi24P3Definition44NamedCarrierActualTwoSectorSmallDefectCorrespondence
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts
open SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts

open SporadicFi24P3Definition44NamedCarrierKleinFourLiteralCorrespondence
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialActualCounts

universe u v w
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
local instance quotientFintype : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {BIndex : Type u} [Fintype BIndex] {e : BIndex → k[X]} (blocks : BlockIdempotentDecomposition e)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
variable (tau : MulAut X)
variable {RowT : Fin 34 → Type v} {RowF : Fin 34 → Type w}
variable [∀ i, Finite (RowT i)] [∀ i, Finite (RowF i)]
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
variable (T : TrivialOrdinaryTableData iota tau RowT BlockD)
variable (F : FaithfulOrdinaryTableData iota RowF)
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)
variable (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
variable (trivialRoles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
variable (faithfulRoles : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
  Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
variable (L : TwoLocalOrdinaryBlockData (iota := iota) (R := R) (Rbar := Rbar)
  (tau := tau) (tauD := T.quotientAut) (hprimeTo := T.primeToCenter) (square := T.square)
  (roles := trivialRoles) (Sglobal := T.primitiveGlobal))
variable (small : SmallDefectNumericalSource iota hinj R)
variable (hDefectTrivial : ∀ j : Fin 4, ∃ H : Subgroup X,
  actualHasDefect R (trivialRoles j.succ).1 H ∧ Nat.card H =
    (if j = 0 then 4 else if j = 1 then 8 else 1))
variable (hDefectFaithful : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
  ∃ H : Subgroup X, actualHasDefect R (faithfulRoles nu hnu 1).1 H ∧ Nat.card H = 8)
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (C : ActualSectorOrdinaryRows iota hinj blocks D
  (1 : CentralSector (k := k) (X := X)) (Fin 108))
variable (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
variable (roots : SameIotaConductorRoot iota 10015005)
variable (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
  SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation.rawEvaluatedRows (iota.lift roots.source_root) r c)
variable (allocation : ∀ r : Fin 108, D.ordinaryBlock (C.character r) =
  (trivialRoles (printedBlockLabel r)).1)
variable (fusion : ∀ c : Fin 91, ∃ x : X, tau (A.representative c).1 =
  x * (A.representative (fullPerm c)).1 * x⁻¹)

open SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralCorrespondence
open SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount

variable (CF : ∀ nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1},
  ActualSectorOrdinaryRows iota hinj blocks D nu.1 (Fin 74))
variable (rootsF : {nu : CentralSector (k := k) (X := X) // nu ≠ 1} →
  SameIotaConductorRoot iota 770385)
variable (valuesF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r c,
  ((CF nu).character r).1 (A.representative c).1 =
    SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation.rawEvaluatedRows
      (iota.lift (rootsF nu).source_root) r c)
variable (allocationF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r,
  D.ordinaryBlock ((CF nu).character r) =
    (faithfulRoles nu.1 nu.2
      (SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData.faithfulPrintedBlockLabel r)).1)


open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open EvenFieldFLZ318FixedTheoremGate EvenFieldFLZSourceConditions
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily (QuotientDataFamily)
open SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily
  (TrivialAmbientDataFamily TrivialAmbientRootFamily)
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne
open SporadicFi24P3Definition44NamedCarrierAllLiteralBrauerCorrespondence

variable (Ccanonical : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
variable {S : Type u} [Group S] [Fintype S]
variable (q : X →* S) (hq : IsUniversalCentralExtension q)
variable (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
variable (hkernel : Nat.card q.ker = 3)
variable (hOuterS : Nat.card (LiteralOuterQuotient S) = 2)
variable (Dzero : DefectZeroReductionSource iota)
variable (Tzero : TrivialWeightSource (p := 2) (X := X))
variable (Bzero :
  letI := R.1.operations.ambientBlockData.fintypeBlock
  DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks Dzero)
variable (lower : QuotientDataFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel))
variable (ambientData : TrivialAmbientDataFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel) hq)
variable (seed : TrivialAmbientRootFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel) hq)
variable (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
variable (fieldSource : SpathCoefficientField 2 k iota.prime)
variable (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
variable (S9495 : Navarro9495BrauerCoveringPrinciple 2 k K)
variable (S820 : Navarro820CyclicBrauerTwistPrinciple 2 k K)

include T F L compatibility decomposition hinverts small hDefectTrivial
  hDefectFaithful D C A roots hvalues allocation fusion CF rootsF valuesF allocationF
  hOuterS Bzero lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820

theorem exists_definition41_of_literal_brauer_values :
    Nonempty (Definition41Witness iota hinj R Ccanonical
      (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel)
      Dzero Tzero) := by
  have hcardCenter : Nat.card (Subgroup.center X) = 3 :=
    center_card_three_of_fullCover q hq hs hna hkernel
  obtain ⟨Omega, hOmega, hblock⟩ :=
    exists_actual_equivariant_of_literal_brauer_values
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (Rbar := Rbar) (tau := tau)
      (T := T) (F := F) (compatibility := compatibility) (decomposition := decomposition)
      (hcardCenter := hcardCenter) (hinverts := hinverts) (trivialRoles := trivialRoles)
      (faithfulRoles := faithfulRoles) (L := L) (small := small)
      (hDefectTrivial := hDefectTrivial) (hDefectFaithful := hDefectFaithful)
      (D := D) (C := C) (A := A) (roots := roots) (hvalues := hvalues)
      (allocation := allocation) (fusion := fusion) (CF := CF) (rootsF := rootsF)
      (valuesF := valuesF) (allocationF := allocationF)
  have hOne := qOne_of_canonical_blockPreservingEquiv
    iota hinj R Ccanonical Omega hblock Dzero Tzero compatibility Bzero
  exact ⟨SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily.ofNormalizedEquiv
    iota hinj R Ccanonical (by decide) q hq hs hna hkernel hOuterS tau decomposition hinverts
    Dzero Tzero Omega hOmega hblock hOne compatibility lower ambientData seed
    extensionPrinciple fieldSource S9295 S9495 S820⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllLiteralTripleCoverFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
