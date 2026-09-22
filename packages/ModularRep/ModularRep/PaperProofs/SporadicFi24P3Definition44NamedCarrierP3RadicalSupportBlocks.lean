import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRawBrauerSupport

/-! Expose the already derived role-one defect and identify bottom-radical
weights with the ordinary defect-zero role before constructing any final map. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3RadicalSupportBlocks
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData
open SporadicFi24P3Definition44NamedCarrierP3LocalDefectCore
open SporadicFi24P3Definition44NamedCarrierP3LocalDefectPrincipal
open SporadicFi24P3Definition44NamedCarrierP3LocalDefectEvaluation
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalRawBrauerSupport
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)

universe u
variable {k K G : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem role_one_has_defect
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
    (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ActualOrdinaryDecomposition iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks)
    (C : FullOrdinaryDegreeTable K G)
    (allocation : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ∀ r, Dordinary.ordinaryBlock (C.character r) = roles (blockLabels r))
    (hZero : letI := R.1.operations.ambientBlockData.fintypeBlock
      IsMaximalCentralBrauerDefect (p := 3) R.1.operations.ambientBlockData.blocks
        (roles 2) (⊥ : Subgroup G))
    (Q : RadicalSubgroup (p := 3) (G := G)) (hQcard : Nat.card Q.1 = 9)
    (defectExponent : InflatedNormalizerBlock (k := k) Q.1 → ℕ)
    (orderLaw : let D := R.1.operations.inflatedNormalizerBlockData Q.1
      letI := D.fintypeBlock
      ∀ b Dsub, navarro417LocalHasDefect (p := 3) D.blocks b Dsub →
        Nat.card Dsub = 3 ^ defectExponent b)
    (existence : let D := R.1.operations.inflatedNormalizerBlockData Q.1
      letI := D.fintypeBlock
      Navarro417LocalDefectExistenceSource Q.1 D.blocks)
    (upper : let D := R.1.operations.inflatedNormalizerBlockData Q.1
      letI := R.1.operations.ambientBlockData.fintypeBlock
      letI := D.fintypeBlock
      Navarro417FirstParagraphUpperDefectSource Q.1 Q.2.isPGroup
        D.blocks R.1.operations.ambientBlockData.blocks
        D.catalogue (derivedInterval R Q) R.1.operations.ambientBlockData.catalogue)
    (theta : LocalDefectZeroCharacter (K := K) Q)
    (rowDefect : defectExponent (R.1.operations.inflateToNormalizer Q.1
      (R.1.operations.localCharacterBlock Q.1 theta.1 theta.2)) = 2) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    Navarro411DefectRepresentative (p := 3)
      R.1.operations.ambientBlockData.blocks (roles 1) Q.1 := by
  let O := R.1.operations
  let D := O.inflatedNormalizerBlockData Q.1
  let A := O.ambientBlockData
  let _ := A.fintypeBlock
  let _ := D.fintypeBlock
  let c := O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2)
  let S414 := derivedInterval R Q
  have hLocal := localHasDefect_copy_of_defectOrder Q.1 Q.2.isPGroup
    D.blocks existence defectExponent orderLaw c (by
      change 3 ^ defectExponent
        (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2)) ≤ Nat.card Q.1
      rw [rowDefect, hQcard]
      norm_num)
  have hExact := inducedBlock_has_exact_defect Q.1 Q.2.isPGroup
    D.blocks A.blocks D.catalogue S414 A.catalogue upper c hLocal
  have hmax := IsMaximalNonzeroPSubgroup.of_nonzero_iff_isSubconjugate
    hExact.isPGroup hExact.support411.nonzero_iff_isSubconjugate
  have halloc := block_eq_role_one_of_defect_nine iota R roles Dordinary C allocation
    hZero (navarro414InducedBlock S414 A.catalogue c) Q.1 hQcard hmax
  simpa only [halloc] using hExact

theorem rawWeightBlock_eq_role_two_of_bot
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
    (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ActualOrdinaryDecomposition iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks)
    (C : FullOrdinaryDegreeTable K G)
    (allocation : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ∀ r, Dordinary.ordinaryBlock (C.character r) = roles (blockLabels r))
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := 3) (X := G))
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (W : CharacterWeight 3 K G) (hbot : W.subgroup = ⊥) :
    R.1.operations.rawWeightBlock W = roles 2 := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let w : ConjugacyClass (p := 3) (K := K) (G := G) :=
    Quotient.mk'' (Quotient.mk'' W)
  have htrivial : radicalClass w =
      RadicalConjugacyClass.trivialClass Tzero.trivialRadical := by
    change (Quotient.mk'' (⟨W.subgroup, W.radical⟩ :
      RadicalSubgroup (p := 3) (G := G))) =
        Quotient.mk'' (⟨⊥, Tzero.trivialRadical⟩ :
          RadicalSubgroup (p := 3) (G := G))
    exact congrArg Quotient.mk'' (Subtype.ext hbot)
  obtain ⟨d, hd⟩ := Tzero.exists_atOne_of_radicalClass_eq_trivial w htrivial
  calc
    R.1.operations.rawWeightBlock W = R.1.weightBlock w := rfl
    _ = R.1.weightBlock (Tzero.atOne d) := congrArg R.1.weightBlock hd.symm
    _ = operationsBlock iota hinj R (Dzero.reduce (iota := iota) d) :=
      atOne_block_of_availability iota hinj R availability Dzero Tzero compatibility d
    _ = brauerBlock iota hinj R.1.operations.ambientBlockData.blocks
        (Dzero.reduce (iota := iota) d) :=
      operationsBlock_eq iota hinj R R.1.operations.ambientBlockData.blocks _
    _ = Dordinary.ordinaryBlock d.1 :=
      brauerBlock_reduce_eq_ordinaryBlock iota hinj
        R.1.operations.ambientBlockData.blocks Dordinary Dzero d
    _ = Dordinary.ordinaryBlock (C.character 93) :=
      congrArg Dordinary.ordinaryBlock ((defectZero_iff_selected C d.1).mp d.2)
    _ = roles 2 := allocation 93

theorem rawWeight_isSubconjugate
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (b : ActualBlock (k := k) (X := G)) (Q : Subgroup G)
    (h411 : letI := R.1.operations.ambientBlockData.fintypeBlock
      Navarro411CentralBrauerSource R.1.operations.ambientBlockData.blocks b Q)
    (W : CharacterWeight 3 K G) (source : CanonicalRawReduction iota W)
    (hW : R.1.operations.rawWeightBlock W = b) :
    W.subgroup.IsSubconjugate Q := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  have hs := rawWeight_has_nonzero_brauer_support iota R compatibility W source
  rw [hW] at hs
  exact (h411.nonzero_iff_isSubconjugate W.subgroup W.radical.isPGroup).mp hs

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3RadicalSupportBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
