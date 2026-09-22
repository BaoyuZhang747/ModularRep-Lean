import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalCompleteCollapse
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse

/-!
# Explicit witnesses for the numerical blockwise construction

These definitions expose the data constructed in the two numerical arguments.
This permits root compatibility to be required for the actual extensions and
intermediate block calculations, without selecting data from a mere existence
statement. The numerical matching is unchanged.
-/

noncomputable section

namespace ManuscriptIBAW.Sporadic.OriginalNumericalWitness

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

/-- Construct the extension and block witnesses for the specified numerical matching.
Root compatibility is a separate condition on these specific witnesses. -/
def witnessOfNumerical
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource p X)
    (allInner : AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (hAWC :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      NumericalBlockwiseAWC (iota := iota) (hinj := hinj)
        (blocks := R.1.operations.ambientBlockData.blocks) (R := R))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C Cover)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Definition41Witness iota hinj R C Cover D T := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let : Finite (GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :=
    Finite.of_injective (D.reduce (iota := iota)) (D.reduce_injective (iota := iota))
  let : Fintype (GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) := Fintype.ofFinite _
  let blocks := R.1.operations.ambientBlockData.blocks
  let Cblock := trivialWeightBlockCompatibilityOfCanonicalOperations iota hinj R C D T compatibility
  let TI := ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityFamily.trivialWeightIdentification (K := K) T
  let Omega := globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := Cblock) TI hAWC
  refine ofNormalizedEquiv iota hinj R C Cover allInner D T
    Omega ?_ ?_ compatibility lower fieldSource
  · intro phi
    exact (globalEquiv_block_preserving
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := Cblock) (TI := TI) (hAWC := hAWC) phi).trans
      (operationsBlock_eq iota hinj R blocks phi).symm
  · exact globalEquiv_normalisation
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := Cblock) (TI := TI) (hAWC := hAWC)

end ManuscriptIBAW.Sporadic.OriginalNumericalWitness



noncomputable section

namespace ManuscriptIBAW.Sporadic.CanonicalNumericalWitness

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

/-- Construct the extension and block witnesses for the specified numerical matching.
Root compatibility is a separate condition on these specific witnesses. -/
def witnessOfNumerical
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource p X) (hc : Subgroup.center X = ⊥)
    (allInner : AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (hAWC :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      NumericalBlockwiseAWC (iota := iota) (hinj := hinj)
        (blocks := R.1.operations.ambientBlockData.blocks) (R := R))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Definition41Witness iota hinj R C Cover hc D T := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let : Finite (GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :=
    Finite.of_injective (D.reduce (iota := iota)) (D.reduce_injective (iota := iota))
  let : Fintype (GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) := Fintype.ofFinite _
  let blocks := R.1.operations.ambientBlockData.blocks
  let Cblock := trivialWeightBlockCompatibilityOfCanonicalOperations iota hinj R C D T compatibility
  let TI := trivialWeightIdentification (K := K) T
  let Omega := globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := Cblock) TI hAWC
  refine ofNormalizedEquiv iota hinj R C Cover hc allInner.eq_conj D T
    Omega ?_ ?_ ?_ compatibility fieldSource
  · exact AllAutomorphismsInner.globalEquiv_equivariant
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := Cblock) (TI := TI) (hAWC := hAWC) allInner
  · intro phi
    exact (globalEquiv_block_preserving
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := Cblock) (TI := TI) (hAWC := hAWC) phi).trans
      (operationsBlock_eq iota hinj R blocks phi).symm
  · exact globalEquiv_normalisation
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := Cblock) (TI := TI) (hAWC := hAWC)

end ManuscriptIBAW.Sporadic.CanonicalNumericalWitness


/-
This file belongs to the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under explicit external assumptions.
-/
