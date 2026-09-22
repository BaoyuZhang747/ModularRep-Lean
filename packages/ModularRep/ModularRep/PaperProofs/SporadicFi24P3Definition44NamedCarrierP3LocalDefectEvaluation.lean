import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectCore
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectPrincipal
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntervalCentralCharacter
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation

/-! Actual local row evaluation from the independently bound local block
defect. All catalogues, ordinary rows and block labels belong to the same R.
The ambient allocation is derived from local defect, not supplied as a source. -/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectEvaluation
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData
open SporadicFi24P3Definition44NamedCarrierP3LocalDefectCore
open SporadicFi24P3Definition44NamedCarrierP3LocalDefectPrincipal
open SporadicFi24P3Definition44NamedCarrierP3IntervalCentralCharacter

universe u
variable {k K G : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

omit [IsAlgClosed k] in
theorem derivedInterval
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (Q : RadicalSubgroup (p := 3) (G := G)) : NormalizerIntervalSource R.1.operations Q := by
  let _ : IsAlgClosed k := R.1.operations.isAlgClosed
  let D := R.1.operations.inflatedNormalizerBlockData Q.1
  let _ := D.fintypeBlock
  exact interval_central_character_source (normalizerCentralBrauerInterval Q.2.isPGroup)
    D.blocks D.catalogue

theorem local_evaluation_from_defect_order
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
    intervalEvaluation R.1.operations Q
      (R.1.operations.inflateToNormalizer Q.1
        (R.1.operations.localCharacterBlock Q.1 theta.1 theta.2)) (roles 1) = 1 := by
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
  have hcc := congrArg
    (fun f : GroupAlgebraCenter k G →ₐ[k] k => f (A.blocks.blockIdempotentInCenter (roles 1)))
    (navarro414InducedBlock_centralCharacter S414 A.catalogue c)
  rw [halloc] at hcc
  exact hcc.symm.trans (A.catalogue.centralCharacter_own (roles 1))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectEvaluation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
