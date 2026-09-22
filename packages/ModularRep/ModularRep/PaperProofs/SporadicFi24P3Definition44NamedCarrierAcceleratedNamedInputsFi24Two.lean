import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-! The named Fi24Two input constructor stores only the checked application's
lower telescope and an explicit named-base equivalence. Its complete certificate
is produced by realise, never supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two
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

open EvenFieldFLZ318FixedTheoremGate
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


open SporadicFi24P3Definition44NamedCarrierTableDerivedLiteralTripleCoverFamily

open ModularRep ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
universe u v w

local instance brauerFintype {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X] (iota : PrimeRegularRootEmbedding p k K X) :
    Fintype (IBr iota) := Fintype.ofFinite _
local instance centerFintype {X : Type u} [Group X] [Fintype X] :
    Fintype (Subgroup.center X) := Fintype.ofFinite _
local instance quotientFintype {X : Type u} [Group X] [Fintype X] :
    Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _

-- The two independent row universes occur in constructor fields.
-- Their maximum is necessarily the universe of the input container.
set_option linter.checkUnivs false in
inductive Inputs (base : NamedBase.{u}) : Type (max (u + 1) (v + 1) (w + 1)) where
  | mk
    {k K X : Type u}
    [inputInst1 : Field k]
    [inputInst2 : Field K]
    [inputInst3 : CharP k 2]
    [inputInst4 : IsAlgClosed k]
    [inputInst5 : CharZero K]
    [inputInst6 : Group X]
    [inputInst7 : Fintype X]
    {S : Type u}
    [inputInst8 : Group S]
    [inputInst9 : Fintype S]
    (q : X →* S)
    (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S)
    (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3)
    (hOuterS : Nat.card (SporadicFi24P3Definition44NamedCarrierActualOuterQuotient.LiteralOuterQuotient S) = 2) :
    letI := centerCardInverseFromCover (k := k) q hq hs hna hkernel
    ∀
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {BIndex : Type u}
    [inputInst10 : Fintype BIndex]
    {e : BIndex → k[X]}
    (blocks : BlockIdempotentDecomposition e)
    (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
    (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
    (tau : MulAut X)
    {RowT : Fin 34 → Type v}
    {RowF : Fin 34 → Type w}
    [_inputInst11 : ∀ i, Finite (RowT i)]
    [_inputInst12 : ∀ i, Finite (RowF i)]
    {BlockD : Type u}
    [inputInst13 : MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
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
    (_Dzero : DefectZeroReductionSource iota)
    (_Tzero : TrivialWeightSource (p := 2) (X := X))
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
    (_S820 : Navarro820CyclicBrauerTwistPrinciple 2 k K)
    (_namedBaseEquiv : ((ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel)).S ≃* base.S), Inputs base

def realise {base : NamedBase.{u}} (I : Inputs.{u, v, w} base) :
    {M : CaseModel base 2 // RawCaseConclusion M} := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 S inputInst8 inputInst9 q hq hs hna hkernel hOuterS iota hinj BIndex inputInst10 e blocks R Rbar tau RowT RowF inputInst11 inputInst12 BlockD inputInst13 T _F _compatibility _decomposition _hinverts trivialRoles faithfulRoles _Lrows _small _hDefectTrivial _hDefectFaithful D C A roots _hvalues _allocation _fusion CF rootsF _valuesF _allocationF Ccanonical _Dzero _Tzero _hsingletonZero _lower _ambientData _seed _extensionPrinciple _fieldSource _S9295 _S9495 _S820 namedBaseEquiv =>
      letI := centerCardInverseFromCover (k := k) q hq hs hna hkernel
      let selectedCover : EllPrimeCoverSource 2 X := (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel)
      let M : CaseModel base 2 := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      refine ⟨M, ?_⟩
      change RawDefinition41Certificate iota R selectedCover
      exact ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications.Fi24Two.definition41_from_external_inputs
        (k := k)
        (K := K)
        (X := X)
        (S := S)
        (q := q)
        (hq := hq)
        (hs := hs)
        (hna := hna)
        (hkernel := hkernel)
        (hOuterS := hOuterS)
        (iota := iota)
        (hinj := hinj)
        (BIndex := BIndex)
        (e := e)
        (blocks := blocks)
        (R := R)
        (Rbar := Rbar)
        (tau := tau)
        (RowT := RowT)
        (RowF := RowF)
        (BlockD := BlockD)
        (T := T)
        (_F := _F)
        (_compatibility := _compatibility)
        (_decomposition := _decomposition)
        (_hinverts := _hinverts)
        (trivialRoles := trivialRoles)
        (faithfulRoles := faithfulRoles)
        (_Lrows := _Lrows)
        (_small := _small)
        (_hDefectTrivial := _hDefectTrivial)
        (_hDefectFaithful := _hDefectFaithful)
        (D := D)
        (C := C)
        (A := A)
        (roots := roots)
        (_hvalues := _hvalues)
        (_allocation := _allocation)
        (_fusion := _fusion)
        (CF := CF)
        (rootsF := rootsF)
        (_valuesF := _valuesF)
        (_allocationF := _allocationF)
        (Ccanonical := Ccanonical)
        (_Dzero := _Dzero)
        (_Tzero := _Tzero)
        (_hsingletonZero := _hsingletonZero)
        (_lower := _lower)
        (_ambientData := _ambientData)
        (_seed := _seed)
        (_extensionPrinciple := _extensionPrinciple)
        (_fieldSource := _fieldSource)
        (_S9295 := _S9295)
        (_S9495 := _S9495)
        (_S820 := _S820)

def model {base : NamedBase.{u}} (I : Inputs.{u, v, w} base) : CaseModel base 2 :=
  (realise I).val

theorem certificate {base : NamedBase.{u}} (I : Inputs.{u, v, w} base) :
    RawCaseConclusion (model I) := (realise I).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
