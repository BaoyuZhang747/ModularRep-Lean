import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllLiteralTripleCoverFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryTableConstructor
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock

/-! The original full-cover family after deriving local metadata, the center inverse,
and the defect-zero reduction block from the original ordinary data. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTableDerivedLiteralTripleCoverFamily

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
open EvenFieldFLZ318FixedTheoremGate
variable {S : Type u} [Group S] [Fintype S]
variable (q : X →* S) (hq : IsUniversalCentralExtension q)
variable (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
variable (hkernel : Nat.card q.ker = 3)
variable (hOuterS : Nat.card (SporadicFi24P3Definition44NamedCarrierActualOuterQuotient.LiteralOuterQuotient S) = 2)
@[instance_reducible]
def centerCardInverseFromCover : Invertible (Fintype.card (Subgroup.center X) : k) :=
  SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel.fixedCentralCardInvertible
    (k := k) (p := 2) (Subgroup.center X) (by
      rw [SporadicFi24P3Definition44NamedCarrierTripleCoverFacts.center_card_three_of_fullCover
        q hq hs hna hkernel]
      decide)
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralCorrespondence
open SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount

open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open EvenFieldFLZ318FixedTheoremGate EvenFieldFLZSourceConditions
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily (QuotientDataFamily)
open SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily
  (TrivialAmbientDataFamily TrivialAmbientRootFamily)
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne
open SporadicFi24P3Definition44NamedCarrierAllLiteralBrauerCorrespondence

open SporadicFi24P3Definition44NamedCarrierAllLiteralTripleCoverFamily
open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryTableConstructor
open SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock


include hOuterS in
theorem exists_definition41_of_tables_and_literal_values :
    letI := centerCardInverseFromCover (k := k) q hq hs hna hkernel
    ∀ (iota : PrimeRegularRootEmbedding 2 k K X)
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      {BIndex : Type u} [Fintype BIndex] {e : BIndex → k[X]} (blocks : BlockIdempotentDecomposition e)
      (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
      (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
      (tau : MulAut X)
      {RowT : Fin 34 → Type v} {RowF : Fin 34 → Type w}
      [∀ i, Finite (RowT i)] [∀ i, Finite (RowF i)]
      {BlockD : Type u} [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
      (T : TrivialOrdinaryTableData iota tau RowT BlockD)
      (_F : FaithfulOrdinaryTableData iota RowF)
      (_compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
      (_decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)
      (_hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
      (trivialRoles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
      (faithfulRoles : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
  Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
      (_Lrows :
  SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryRowData.TwoLocalOrdinaryRowData
    (iota := iota) (R := R) (Rbar := Rbar) (hprimeTo := T.primeToCenter)
    (roles := trivialRoles) (Sglobal := T.primitiveGlobal))
      (_small : SmallDefectNumericalSource iota hinj R)
      (_hDefectTrivial : ∀ j : Fin 4, ∃ H : Subgroup X,
  actualHasDefect R (trivialRoles j.succ).1 H ∧ Nat.card H =
    (if j = 0 then 4 else if j = 1 then 8 else 1))
      (_hDefectFaithful : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
  ∃ H : Subgroup X, actualHasDefect R (faithfulRoles nu hnu 1).1 H ∧ Nat.card H = 8)
      (D : ActualOrdinaryDecomposition iota hinj blocks)
      (C : ActualSectorOrdinaryRows iota hinj blocks D
  (1 : CentralSector (k := k) (X := X)) (Fin 108))
      (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
      (roots : SameIotaConductorRoot iota 10015005)
      (_hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
  SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation.rawEvaluatedRows (iota.lift roots.source_root) r c)
      (_allocation : ∀ r : Fin 108, D.ordinaryBlock (C.character r) =
  (trivialRoles (printedBlockLabel r)).1)
      (_fusion : ∀ c : Fin 91, ∃ x : X, tau (A.representative c).1 =
  x * (A.representative (fullPerm c)).1 * x⁻¹)
      (CF : ∀ nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1},
  ActualSectorOrdinaryRows iota hinj blocks D nu.1 (Fin 74))
      (rootsF : {nu : CentralSector (k := k) (X := X) // nu ≠ 1} →
  SameIotaConductorRoot iota 770385)
      (_valuesF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r c,
  ((CF nu).character r).1 (A.representative c).1 =
    SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation.rawEvaluatedRows
      (iota.lift (rootsF nu).source_root) r c)
      (_allocationF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r,
  D.ordinaryBlock ((CF nu).character r) =
    (faithfulRoles nu.1 nu.2
      (SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData.faithfulPrintedBlockLabel r)).1)
      (Ccanonical : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
      (Dzero : DefectZeroReductionSource iota)
      (Tzero : TrivialWeightSource (p := 2) (X := X))
      (_hsingletonZero :
  ∀ d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := X),
    Subsingleton {phi : IBr iota // brauerBlock iota hinj blocks phi = D.ordinaryBlock d.1})
      (_lower : QuotientDataFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel))
      (_ambientData : TrivialAmbientDataFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel) hq)
      (_seed : TrivialAmbientRootFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel) hq)
      (_extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
      (_fieldSource : SpathCoefficientField 2 k iota.prime)
      (_S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
      (_S9495 : Navarro9495BrauerCoveringPrinciple 2 k K)
      (_S820 : Navarro820CyclicBrauerTwistPrinciple 2 k K),
    Nonempty (Definition41Witness iota hinj R Ccanonical
      (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel)
      Dzero Tzero) := by
  let := centerCardInverseFromCover (k := k) q hq hs hna hkernel
  intro iota hinj BIndex instBIndex e blocks R Rbar tau RowT RowF
    instRowsT instRowsF BlockD instBlockD T F compatibility decomposition hinverts
    trivialRoles faithfulRoles Lrows small hDefectTrivial hDefectFaithful D C A
    roots hvalues allocation fusion CF rootsF valuesF allocationF Ccanonical
    Dzero Tzero hsingletonZero lower ambientData seed extensionPrinciple fieldSource
    S9295 S9495 S820
  let L := of_table_and_rows iota R Rbar tau T trivialRoles Lrows
  let Bzero := canonicalDefectZeroBlockSource iota hinj blocks R D Dzero hsingletonZero
  exact exists_definition41_of_literal_brauer_values
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (Rbar := Rbar) (tau := tau)
    (T := T) (F := F) (compatibility := compatibility) (decomposition := decomposition)
    (hinverts := hinverts) (trivialRoles := trivialRoles) (faithfulRoles := faithfulRoles)
    (L := L) (small := small) (hDefectTrivial := hDefectTrivial) (hDefectFaithful := hDefectFaithful)
    (D := D) (C := C) (A := A) (roots := roots) (hvalues := hvalues)
    (allocation := allocation) (fusion := fusion) (CF := CF) (rootsF := rootsF)
    (valuesF := valuesF) (allocationF := allocationF)
    (Ccanonical := Ccanonical) (q := q) (hq := hq) (hs := hs) (hna := hna)
    (hkernel := hkernel) (hOuterS := hOuterS) (Dzero := Dzero) (Tzero := Tzero)
    (Bzero := Bzero) (lower := lower) (ambientData := ambientData) (seed := seed)
    (extensionPrinciple := extensionPrinciple) (fieldSource := fieldSource)
    (S9295 := S9295) (S9495 := S9495) (S820 := S820)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTableDerivedLiteralTripleCoverFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
