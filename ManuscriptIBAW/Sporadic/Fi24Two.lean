import ModularRep.PaperProofs.CoherentOriginalPacketChoices
import ManuscriptIBAW.Sporadic.Fi24TwoWeights
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialActualCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne

/-!
# The Fi24′ case at two

The covering group, root embedding and specified character and block
operations determine the model before the proof. The invariant subset
argument constructs an equivariant block preserving matching. The ambient ordinary
table values, their block labels and the action on classes remain explicit
computation and interpretation assumptions. The full condition additionally
assumes the existence of compatible extension and block witnesses for the
same specified correspondence. These witnesses are not deduced from the
raw extension construction by the numerical argument.
No allocation of local weight
characters to blocks is supplied.
-/

noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ManuscriptIBAW.Sporadic.Fi24Two
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero ModularRep.PaperProofs
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts
open SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierAllPairs

open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts
open SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts

open SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialActualCounts

open EvenFieldFLZ318FixedTheoremGate
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

open SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock



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

@[instance_reducible]
def centerCardInverseFromCover {k X S : Type u} [Field k] [CharP k 2]
    [Group X] [Fintype X] [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3) : Invertible (Fintype.card (Subgroup.center X) : k) :=
  SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel.fixedCentralCardInvertible
    (k := k) (p := 2) (Subgroup.center X) (by
      rw [center_card_three_of_fullCover q hq hs hna hkernel]
      decide)

set_option linter.checkUnivs false in
inductive SourceInputs (base : NamedBase.{u}) : Type (max (u + 1) (v + 1) (w + 1)) where
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
    (geometry : Fi24TwoSupport.Geometry iota R T trivialRoles)
    (_small : SmallDefectNumericalSource iota hinj R)
    (_hDefectZero : ∀ j : Fin 2, ∃ H : Subgroup X,
      actualHasDefect R (trivialRoles (zeroRole j)).1 H ∧ Nat.card H = 1)
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
    (_namedBaseEquiv : ((ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel)).S ≃* base.S), SourceInputs base

namespace SourceInputs

def model {base : NamedBase.{u}} (I : SourceInputs.{u, v, w} base) : CaseModel base 2 := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 S inputInst8 inputInst9 q hq hs hna hkernel hOuterS iota hinj BIndex inputInst10 e blocks R tau RowT RowF inputInst11 inputInst12 BlockD inputInst13 T _F _compatibility _decomposition _hinverts trivialRoles faithfulRoles geometry _small _hDefectZero _hDefectFaithful D C A roots _hvalues _allocation _fusion CF rootsF _valuesF _allocationF Ccanonical _Dzero _Tzero _hsingletonZero _lower _ambientData _seed _extensionPrinciple _fieldSource _S9295 _S9495 _S820 namedBaseEquiv =>
      exact {
        k := k
        K := K
        X := X
        iota := iota
        R := R
        Cover := ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel
        baseEquiv := namedBaseEquiv }

/-- Bijections with the equivariance and block preservation supplied by the
ordinary table calculation. -/
def Matching {base : NamedBase.{u}} (I : SourceInputs.{u, v, w} base) :=
  let M := I.model
  letI := M.fintypeX
  {Omega : IBr M.iota ≃ WeightClass (p := 2) (K := M.K) (X := M.X) //
    (∀ (a : (MulAut M.X)ᵐᵒᵖ) (phi : IBr M.iota), Omega (a • phi) = a • Omega phi) ∧
    ∀ phi, M.R.1.weightBlock (Omega phi) = operationsBlock M.iota
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding M.iota) M.R phi}

/-- The existing invariant subset and table arguments construct the matching. -/
theorem matching_exists {base : NamedBase.{u}} (I : SourceInputs.{u, v, w} base) :
    Nonempty I.Matching := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 S inputInst8 inputInst9 q hq hs hna hkernel hOuterS iota hinj BIndex inputInst10 e blocks R tau RowT RowF inputInst11 inputInst12 BlockD inputInst13 T _F _compatibility _decomposition _hinverts trivialRoles faithfulRoles geometry _small _hDefectZero _hDefectFaithful D C A roots _hvalues _allocation _fusion CF rootsF _valuesF _allocationF Ccanonical _Dzero _Tzero _hsingletonZero _lower _ambientData _seed _extensionPrinciple _fieldSource _S9295 _S9495 _S820 namedBaseEquiv =>
      let := centerCardInverseFromCover (k := k) q hq hs hna hkernel
      have hBr41 := actualTrivialSector_card_fortyOne_of_literal_values
        iota hinj blocks D C A roots _hvalues
      have hBr31 := actualTrivialSector_fixed_card_thirtyOne_of_literal_values
        iota hinj blocks D C A roots _hvalues tau _decomposition _fusion
      have hK4 : actualBrauerSignature iota hinj blocks tau (trivialRoles 1).1 = (3, 1) := by
        apply Prod.ext
        · exact actualKleinFourBlock_card_three_of_literal_values
            iota hinj blocks D C trivialRoles _allocation A roots _hvalues
        · exact actualKleinFourBlock_fixed_card_one_of_literal_values
            iota hinj blocks D C trivialRoles _allocation A roots _hvalues tau _decomposition _fusion
      have hD8 : actualBrauerSignature iota hinj blocks tau (trivialRoles 2).1 = (3, 3) := by
        apply Prod.ext
        · exact actualDihedralBlock_card_three_of_literal_values
            iota hinj blocks D C trivialRoles _allocation A roots _hvalues
        · exact actualDihedralBlock_fixed_card_three_of_literal_values
            iota hinj blocks D C trivialRoles _allocation A roots _hvalues tau _fusion
      have hZero : ∀ j : Fin 2,
          actualBrauerSignature iota hinj blocks tau (trivialRoles (zeroRole j)).1 = (1, 1) := by
        intro j
        apply Prod.ext
        · exact actualZeroBlock_card_one_of_literal_values
            iota hinj blocks D C trivialRoles _allocation A roots _hvalues j
        · exact actualZeroBlock_fixed_card_one_of_literal_values
            iota hinj blocks D C trivialRoles _allocation A roots _hvalues j tau _fusion
      have hBrOther : ∀ j : Fin 4,
          actualBrauerSignature iota hinj blocks tau (trivialRoles j.succ).1 =
            nonprincipalSignature j := by
        intro j
        fin_cases j
        · simpa [nonprincipalSignature] using hK4
        · simpa [nonprincipalSignature] using hD8
        · simpa [nonprincipalSignature, zeroRole] using hZero 0
        · simpa [nonprincipalSignature, zeroRole] using hZero 1
      have hDefect : ∀ j : Fin 4, ∃ H : Subgroup X,
          actualHasDefect R (trivialRoles j.succ).1 H ∧ Nat.card H =
            (if j = 0 then 4 else if j = 1 then 8 else 1) := by
        intro j
        fin_cases j
        · exact ⟨geometry.D4, geometry.defect4, geometry.order4⟩
        · exact ⟨geometry.D8, geometry.defect8, geometry.order8⟩
        · simpa [zeroRole] using _hDefectZero 0
        · simpa [zeroRole] using _hDefectZero 1
      have hfixed := Fi24TwoWeights.fixed_counts iota hinj blocks R tau T _compatibility
        trivialRoles geometry D Ccanonical _Dzero _Tzero _hsingletonZero
        _decomposition hBrOther _small hDefect
      have hWtOther := nonprincipal_weight_signatures_of_two_fixed_counts
        iota hinj blocks R tau trivialRoles hBrOther _small hDefect hfixed.1 hfixed.2
      have hBr25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
          Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = 25 := by
        intro nu hnu
        exact actualFaithfulSector_card_twentyFive_of_literal_values
          iota hinj blocks D ⟨nu, hnu⟩ (CF ⟨nu, hnu⟩) A
          (rootsF ⟨nu, hnu⟩) (_valuesF ⟨nu, hnu⟩)
      have hBrSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
          Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi =
            (faithfulRoles nu hnu 1).1} = 2 := by
        intro nu hnu
        exact actualFaithfulSmallBlock_card_two_of_literal_values
          iota hinj blocks D ⟨nu, hnu⟩ (CF ⟨nu, hnu⟩)
          (faithfulRoles nu hnu) (_allocationF ⟨nu, hnu⟩) A
          (rootsF ⟨nu, hnu⟩) (_valuesF ⟨nu, hnu⟩)
      have hWtSmall := faithful_small_weight_totals iota hinj blocks R _small
        faithfulRoles _hDefectFaithful hBrSmall
      obtain ⟨Omega, hOmega, hblock⟩ := exists_actual_equivariant_of_ordinary_tables
        iota hinj blocks R tau T _F _compatibility _decomposition
        (center_card_three_of_fullCover q hq hs hna hkernel) _hinverts
        trivialRoles faithfulRoles hBr41 hBr31 hBrOther hWtOther hBr25 hBrSmall hWtSmall
      exact ⟨⟨Omega, hOmega, hblock⟩⟩

/-- A specified matching from the numerical proof. No extension packet is chosen here. -/
def numericalMatching {base : NamedBase.{u}} (I : SourceInputs.{u, v, w} base) : I.Matching :=
  Classical.choice I.matching_exists

/-- The only additional packet obligation concerns the specified numerical matching.
Its compatible extensions and intermediate block witnesses remain external. -/
def PacketCompatibility {base : NamedBase.{u}} (I : SourceInputs.{u, v, w} base) : Prop := by
  let matching := I.numericalMatching
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 S inputInst8 inputInst9 q hq hs hna hkernel hOuterS iota hinj BIndex inputInst10 e blocks R tau RowT RowF inputInst11 inputInst12 BlockD inputInst13 T _F _compatibility _decomposition _hinverts trivialRoles faithfulRoles geometry _small _hDefectZero _hDefectFaithful D C A roots _hvalues _allocation _fusion CF rootsF _valuesF _allocationF Ccanonical _Dzero _Tzero _hsingletonZero _lower _ambientData _seed _extensionPrinciple _fieldSource _S9295 _S9495 _S820 namedBaseEquiv =>
      exact CoherentOriginalPacketChoices.OriginalPacketChoices iota hinj R Ccanonical matching.1

theorem complete {base : NamedBase.{u}} (I : SourceInputs.{u, v, w} base)
    (packets : I.PacketCompatibility) : CaseConclusion I.model := by
  let matching := I.numericalMatching
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 S inputInst8 inputInst9 q hq hs hna hkernel hOuterS iota hinj BIndex inputInst10 e blocks R tau RowT RowF inputInst11 inputInst12 BlockD inputInst13 T _F _compatibility _decomposition _hinverts trivialRoles faithfulRoles geometry _small _hDefectZero _hDefectFaithful D C A roots _hvalues _allocation _fusion CF rootsF _valuesF _allocationF Ccanonical _Dzero _Tzero _hsingletonZero _lower _ambientData _seed _extensionPrinciple _fieldSource _S9295 _S9495 _S820 namedBaseEquiv =>
      let := centerCardInverseFromCover (k := k) q hq hs hna hkernel
      change Definition41Certificate iota R
        (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel)
      let Omega := matching.1
      have hOmega := matching.2.1
      have hblock := matching.2.2
      let Bzero := canonicalDefectZeroBlockSource iota hinj blocks R D _Dzero _hsingletonZero
      have hOne := qOne_of_canonical_blockPreservingEquiv
        iota hinj R Ccanonical Omega hblock _Dzero _Tzero _compatibility Bzero
      exact CoherentOriginalPacketChoices.of_original_with_packet_choices
        iota R Ccanonical _ _Dzero _Tzero
        (SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily.ofNormalizedEquiv
          iota hinj R Ccanonical (by decide) q hq hs hna hkernel hOuterS tau _decomposition _hinverts
          _Dzero _Tzero Omega hOmega hblock hOne _compatibility _lower _ambientData _seed
          _extensionPrinciple _fieldSource _S9295 _S9495 _S820)
        packets

end SourceInputs

/-- Numerical and structural sources, together with compatible packets for
the matching selected by their numerical argument. -/
structure Inputs (base : NamedBase.{u}) where
  source : SourceInputs.{u, v, w} base
  packets : source.PacketCompatibility

namespace Inputs

def model {base : NamedBase.{u}} (I : Inputs.{u, v, w} base) : CaseModel base 2 :=
  I.source.model

theorem complete {base : NamedBase.{u}} (I : Inputs.{u, v, w} base) :
    CaseConclusion I.model := I.source.complete I.packets

def realise {base : NamedBase.{u}} (I : Inputs.{u, v, w} base) :
    {M : CaseModel base 2 // CaseConclusion M} := ⟨I.model, I.complete⟩

end Inputs

end ManuscriptIBAW.Sporadic.Fi24Two

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
