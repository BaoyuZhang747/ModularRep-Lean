import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameMapQOne
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock

/-! Defect-zero total and fixed counts before blockwise cancellation.
The ordinary radical-bottom principle remains explicit; the fibre
equivalence and its singleton cardinalities are constructed internally. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectZeroCounts

open ModularRep
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource DefectZeroWeightSubgroupSource
    defectZeroBrauerFibre_subsingleton defectZeroBlockFibreEquiv)
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock

universe u

theorem actual_defectZero_signature
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (B : letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D)
    (Z : letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroWeightSubgroupSource iota hinj
        R.1.operations.ambientBlockData.blocks (R := R) D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
    (b : ActualBlock (k := k) (X := X))
    (hd : operationsBlock iota hinj R (D.reduce (iota := iota) d) = b)
    (tau : MulAut X) (hb : MulOpposite.op tau • b = b) :
    (Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b} = 1) ∧
    (Nat.card {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b} = 1) ∧
    (Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b ∧
      MulOpposite.op tau • phi = phi} = 1) ∧
    (Nat.card {w : WeightClass (p := p) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w} = 1) := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  let bs := R.1.operations.ambientBlockData.blocks
  have COne := trivialWeightBlockCompatibilityOfCanonicalOperations
    iota hinj R (rawReductionOfAvailability iota availability) D T compatibility
  have hbd : brauerBlock iota hinj bs (D.reduce (iota := iota) d) = b :=
    (operationsBlock_eq iota hinj R bs (D.reduce (iota := iota) d)).symm.trans hd
  have hsub := defectZeroBrauerFibre_subsingleton
    (iota := iota) (hinj := hinj) (blocks := bs) D B d
  have hBrOne0 : Nat.card {phi : IBr iota //
      brauerBlock iota hinj bs phi = brauerBlock iota hinj bs (D.reduce (iota := iota) d)} = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨D.reduce (iota := iota) d, rfl⟩⟩⟩
  let E := defectZeroBlockFibreEquiv
    (iota := iota) (hinj := hinj) (blocks := bs) (R := R) D T COne B Z d
  have hWtOne0 : Nat.card {w : WeightClass (p := p) (K := K) (X := X) //
      R.1.weightBlock w = brauerBlock iota hinj bs (D.reduce (iota := iota) d)} = 1 :=
    (Nat.card_congr E).symm.trans hBrOne0
  have hBrOne : Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b} = 1 := by
    simpa only [operationsBlock_eq iota hinj R bs, hbd] using hBrOne0
  have hWtOne : Nat.card {w : WeightClass (p := p) (K := K) (X := X) //
      R.1.weightBlock w = b} = 1 := by
    simpa only [hbd] using hWtOne0
  have hBrFixed : Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b ∧
      MulOpposite.op tau • phi = phi} = 1 := by
    apply fixed_card_one_of_invariant_singleton (fun phi => MulOpposite.op tau • phi)
      (fun phi => operationsBlock iota hinj R phi = b) _ hBrOne
    intro phi hphi
    exact ((operationsBrauerSupport iota hinj R (MulOpposite.op tau) phi).trans
      (congrArg (fun c : ActualBlock (k := k) (X := X) => MulOpposite.op tau • c) hphi)).trans hb
  exact ⟨hBrOne, hWtOne, hBrFixed,
    weight_fixed_card_one_of_singleton R tau b hb hWtOne⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectZeroCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
