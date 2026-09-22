import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
import ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual

/-! Any original block-preserving equivalence has the required literal
Q=1 normalization, by defect-zero block uniqueness and the canonically
derived at-one block relation. No correspondence is replaced. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter
    TrivialWeightBlockCompatibility)
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource blockEquiv_literal_qOne_normalisation)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock

universe u

theorem qOne_of_blockPreservingEquiv
    {p : ℕ} {k K X BlockIndex : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X] [Fintype BlockIndex]
    {blockIdempotent : BlockIndex → k[X]}
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (COne : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (Bzero : DefectZeroOrdinaryBlockSource iota hinj blocks D) :
    ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d := by
  intro d
  let b := brauerBlock iota hinj blocks (D.reduce (iota := iota) d)
  let e :
      {phi : IBr iota // brauerBlock iota hinj blocks phi = b} ≃
      {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b} :=
    Omega.subtypeEquiv (fun phi => by rw [hblock phi])
  change (e ⟨D.reduce (iota := iota) d, rfl⟩).1 = T.atOne d
  exact blockEquiv_literal_qOne_normalisation
    (iota := iota) (hinj := hinj) (blocks := blocks) D T COne Bzero d e

theorem qOne_of_canonical_blockPreservingEquiv
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (Bzero :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D) :
    ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let blocks := R.1.operations.ambientBlockData.blocks
  have COne : TrivialWeightBlockCompatibility iota hinj blocks R D T :=
    trivialWeightBlockCompatibilityOfCanonicalOperations iota hinj R C D T compatibility
  have hblock' : ∀ phi, R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi := by
    intro phi
    exact (hblock phi).trans (operationsBlock_eq iota hinj R blocks phi)
  exact qOne_of_blockPreservingEquiv iota hinj blocks R Omega hblock' D T COne Bzero

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
