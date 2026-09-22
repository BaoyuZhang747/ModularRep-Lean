import ModularRep.DefectNormalizerCarrier
import ModularRep.Navarro414IntervalCentralCharacterAdapter
import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-!
# Ordinary rows allocated by one interval scalar test

An exhaustive local ordinary catalogue and the actual interval evaluation
on a target primitive determine the representative fibre. The input does
not contain an induced ambient-block equality or a weight count.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u v

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [hclosed : IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fact p.Prime]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]

local instance subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H

abbrev NormalizerIntervalSource
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) : Prop :=
  let D := O.inflatedNormalizerBlockData Q.1
  let _ := D.fintypeBlock
  Navarro414IntervalCentralCharacterSource
    (normalizerCentralBrauerInterval Q.2.isPGroup) D.blocks D.catalogue

def intervalEvaluation
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G))
    (c : InflatedNormalizerBlock (k := k) Q.1) (b : Block) : k :=
  let D := O.inflatedNormalizerBlockData Q.1
  let _ := D.fintypeBlock
  let _ := O.ambientBlockData.fintypeBlock
  let I := normalizerCentralBrauerInterval Q.2.isPGroup
  D.catalogue.centralCharacter c
    (centralBrauerMapTo (k := k) (p := p) Q.1 (defectNormalizer Q.1)
      I.isPGroup I.centralizer_le I.le_normalizer
      (O.ambientBlockData.blocks.blockIdempotentInCenter b))

omit hclosed [MulAction (MulAut G)ᵐᵒᵖ Block] in
theorem rawWeightBlock_eq_iff_intervalEvaluation
    (iota : PrimeRegularRootEmbedding p k K G)
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G))
    (theta : LocalDefectZeroCharacter (K := K) Q) (b : Block)
    (S414 : NormalizerIntervalSource O Q) :
    O.rawWeightBlock (characterWeightAt iota.prime Q theta) = b ↔
      intervalEvaluation O Q
        (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2)) b = 1 := by
  let _ : IsAlgClosed k := O.isAlgClosed
  let W := characterWeightAt iota.prime Q theta
  let N := defectNormalizer Q.1
  let D := O.inflatedNormalizerBlockData Q.1
  let A := O.ambientBlockData
  let _ := D.fintypeBlock
  let _ := A.fintypeBlock
  let c := O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2)
  let z := A.blocks.blockIdempotentInCenter b
  have heval : A.catalogue.centralCharacter (O.rawWeightBlock W) z =
      intervalEvaluation O Q c b := by
    calc
      _ = inducedCentralFunction N (D.catalogue.centralCharacter c) z :=
        congrArg (fun lambda : GroupAlgebraCenter k G →ₐ[k] k => lambda z)
          (inducedBlock_centralCharacter N D.catalogue A.catalogue c (O.blockInductionDefined W))
      _ = intervalEvaluation O Q c b :=
        LinearMap.congr_fun (S414.inducedCentralFunction_eq_intervalBrauer c) z
  constructor
  · intro h
    calc
      intervalEvaluation O Q c b = A.catalogue.centralCharacter (O.rawWeightBlock W) z :=
        heval.symm
      _ = 1 := by
        rw [h]
        exact A.catalogue.centralCharacter_own b
  · intro h
    by_contra hne
    have hv : A.catalogue.centralCharacter (O.rawWeightBlock W) z = 1 := heval.trans h
    rw [A.catalogue.centralCharacter_other hne] at hv
    exact zero_ne_one hv

def hitRowsEquivRepresentativeDZ {Row : Type v}
    (iota : PrimeRegularRootEmbedding p k K G)
    (R : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block)
    (rows : Row → LocalDefectZeroCharacter (K := K) Q)
    (rowInjective : Function.Injective rows) (rowSurjective : Function.Surjective rows)
    (C : ∀ r : Row, CanonicalRawReduction iota (characterWeightAt iota.prime Q (rows r)))
    (compatibility : CanonicalLocalBlockCompatibility iota R.operations)
    (S414 : NormalizerIntervalSource R.operations Q) (hit : Row → Bool)
    (evaluation : ∀ r : Row,
      intervalEvaluation R.operations Q
        (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          R.operations Q.1 (C r).normalizerRoot (C r).localBrauer) b =
        if hit r then (1 : k) else 0) :
    {r : Row // hit r = true} ≃ RepresentativeDZ iota.prime R Q b := by
  classical
  let E : Row ≃ LocalDefectZeroCharacter (K := K) Q :=
    Equiv.ofBijective rows ⟨rowInjective, rowSurjective⟩
  have halloc (r : Row) :
      R.operations.rawWeightBlock (characterWeightAt iota.prime Q (rows r)) = b ↔
        hit r = true := by
    have hlocal :
        NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          R.operations Q.1 (C r).normalizerRoot (C r).localBrauer =
        R.operations.inflateToNormalizer Q.1
          (R.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2) :=
      compatibility.normalizerBrauerBlock_eq_inflateToNormalizer
        (characterWeightAt iota.prime Q (rows r)) (C r)
    have hscalar : intervalEvaluation R.operations Q
        (R.operations.inflateToNormalizer Q.1
          (R.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2)) b =
        if hit r then (1 : k) else 0 := by
      rw [← hlocal]
      exact evaluation r
    rw [rawWeightBlock_eq_iff_intervalEvaluation iota R.operations Q (rows r) b S414, hscalar]
    cases hit r <;> simp
  exact E.subtypeEquiv (fun r => (halloc r).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
