import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

/-! Derive the defect-zero reduction's specified block from the global ordinary
decomposition. The independent defect-zero singleton theorem remains explicit. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)

universe u
variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

theorem brauerBlock_reduce_eq_ordinaryBlock
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Dordinary : ActualOrdinaryDecomposition iota hinj blocks)
    (Dzero : DefectZeroReductionSource iota)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    brauerBlock iota hinj blocks (Dzero.reduce (iota := iota) d) =
      Dordinary.ordinaryBlock d.1 := by
  classical
  let phi := Dzero.reduce (iota := iota) d
  have hcolumns : Dordinary.decomposition.columns d.1 = Finsupp.single phi (1 : K) := by
    apply (irreducibleBrauerCharacters_linearIndependent iota).finsuppLinearCombination_injective
    calc
      Finsupp.linearCombination K (actualBrauerFunction iota)
          (Dordinary.decomposition.columns d.1) = actualOrdinaryRestriction (p := p) d.1 :=
        (Dordinary.decomposition.ordinary_eq_decomposition d.1).symm
      _ = actualBrauerFunction iota phi := by
        funext g
        exact Dzero.reduce_isReduction (iota := iota) d g
      _ = Finsupp.linearCombination K (actualBrauerFunction iota)
          (Finsupp.single phi (1 : K)) := by simp
  have hcoeff : Dordinary.decomposition.columns d.1 phi ≠ 0 := by
    rw [hcolumns, Finsupp.single_eq_same]
    exact one_ne_zero
  exact (Dordinary.decomposition.column_support d.1 phi hcoeff).symm

theorem canonicalBrauerBlock_reduce_eq_ordinaryBlock
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (Dordinary : ActualOrdinaryDecomposition iota hinj blocks)
    (Dzero : DefectZeroReductionSource iota)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    brauerBlock iota hinj R.1.operations.ambientBlockData.blocks
      (Dzero.reduce (iota := iota) d) = Dordinary.ordinaryBlock d.1 := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  calc
    brauerBlock iota hinj R.1.operations.ambientBlockData.blocks
        (Dzero.reduce (iota := iota) d) =
        operationsBlock iota hinj R (Dzero.reduce (iota := iota) d) :=
      (operationsBlock_eq iota hinj R R.1.operations.ambientBlockData.blocks _).symm
    _ = brauerBlock iota hinj blocks (Dzero.reduce (iota := iota) d) :=
      operationsBlock_eq iota hinj R blocks _
    _ = Dordinary.ordinaryBlock d.1 :=
      brauerBlock_reduce_eq_ordinaryBlock iota hinj blocks Dordinary Dzero d

def canonicalDefectZeroBlockSource
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (Dordinary : ActualOrdinaryDecomposition iota hinj blocks)
    (Dzero : DefectZeroReductionSource iota)
    (hsingle : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Subsingleton {phi : IBr iota // brauerBlock iota hinj blocks phi = Dordinary.ordinaryBlock d.1}) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks Dzero := by
  letI := R.1.operations.ambientBlockData.fintypeBlock
  refine {
    ordinaryBlock := fun d => Dordinary.ordinaryBlock d.1
    reduction_block := canonicalBrauerBlock_reduce_eq_ordinaryBlock iota hinj blocks R Dordinary Dzero
    brauerFibre_subsingleton := ?_ }
  intro d
  let := hsingle d
  refine ⟨?_⟩
  intro phi psi
  have htransfer (chi : IBr iota) :
      brauerBlock iota hinj blocks chi =
        brauerBlock iota hinj R.1.operations.ambientBlockData.blocks chi :=
    (operationsBlock_eq iota hinj R blocks chi).symm.trans
      (operationsBlock_eq iota hinj R R.1.operations.ambientBlockData.blocks chi)
  have heq : (⟨phi.1, (htransfer phi.1).trans phi.2⟩ :
      {chi : IBr iota // brauerBlock iota hinj blocks chi = Dordinary.ordinaryBlock d.1}) =
        ⟨psi.1, (htransfer psi.1).trans psi.2⟩ := Subsingleton.elim _ _
  apply Subtype.ext
  exact congrArg (fun chi : {chi : IBr iota //
    brauerBlock iota hinj blocks chi = Dordinary.ordinaryBlock d.1} => chi.1) heq

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
