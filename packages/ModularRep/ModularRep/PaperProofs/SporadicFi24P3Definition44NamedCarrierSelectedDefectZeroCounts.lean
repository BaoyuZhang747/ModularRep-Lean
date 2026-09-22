import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameMapQOne
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock

/-! Defect-zero total and fixed counts before blockwise cancellation.
The selected radical-bottom property is derived from three independent
normalizer defect principles and maximal Brauer support at the nominated
ambient block. No uniform defect-zero weight-subgroup source is assumed. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedDefectZeroCounts

open ModularRep
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource defectZeroBrauerFibre_subsingleton)
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock

open SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport

universe u

theorem selected_defectZero_signature
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X] [Fact p.Prime]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (B : letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D)
    (SDefects : RadicalNormalizerDefectSources R)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
    (b : ActualBlock (k := k) (X := X))
    (hDefect : letI := R.1.operations.ambientBlockData.fintypeBlock
      IsMaximalCentralBrauerDefect (p := p) R.1.operations.ambientBlockData.blocks b
        (⊥ : Subgroup X))
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
  have hBot (W : CharacterWeight p K X)
      (hW : R.1.operations.rawWeightBlock W = brauerBlock iota hinj bs (D.reduce (iota := iota) d)) :
      W.subgroup = ⊥ :=
    rawWeight_subgroup_eq_bot R SDefects b hDefect W (hW.trans hbd)
  have hUnique (w : WeightClass (p := p) (K := K) (X := X))
      (hw : R.1.weightBlock w = brauerBlock iota hinj bs (D.reduce (iota := iota) d)) :
      w = T.atOne d := by
    have htrivial : CharacterWeight.radicalClass w =
        CharacterWeight.RadicalConjugacyClass.trivialClass T.trivialRadical := by
      refine Quotient.inductionOn w ?_ hw
      intro w0 hw0
      refine Quotient.inductionOn w0 ?_ hw0
      intro W hW
      have hQ := hBot W (by
        simpa only [CharacterWeight.LocalBlockInductionSource.weightBlock_mk] using hW)
      rw [CharacterWeight.radicalClass_mk]
      exact congrArg
        (fun q : CharacterWeight.RadicalSubgroup (p := p) (G := X) =>
          (Quotient.mk'' q : CharacterWeight.RadicalConjugacyClass (p := p) (G := X)))
        (Subtype.ext hQ)
    obtain ⟨d', hd'⟩ := T.exists_atOne_of_radicalClass_eq_trivial w htrivial
    have hblock : brauerBlock iota hinj bs (D.reduce (iota := iota) d') =
        brauerBlock iota hinj bs (D.reduce (iota := iota) d) := by
      calc
        brauerBlock iota hinj bs (D.reduce (iota := iota) d') = R.1.weightBlock (T.atOne d') :=
          (COne.block_atOne d').symm
        _ = R.1.weightBlock w := congrArg R.1.weightBlock hd'
        _ = brauerBlock iota hinj bs (D.reduce (iota := iota) d) := hw
    have hreduce := DefectZeroOrdinaryBlockSource.uniqueBrauer
      (iota := iota) (hinj := hinj) (blocks := bs) D B d (D.reduce (iota := iota) d') hblock
    have hdd : d' = d := D.reduce_injective (iota := iota) hreduce
    exact hd'.symm.trans (congrArg T.atOne hdd)
  have hWtSub : Subsingleton {w : WeightClass (p := p) (K := K) (X := X) //
      R.1.weightBlock w = brauerBlock iota hinj bs (D.reduce (iota := iota) d)} := by
    constructor
    intro x y
    apply Subtype.ext
    exact (hUnique x.val x.property).trans (hUnique y.val y.property).symm
  have hWtOne0 : Nat.card {w : WeightClass (p := p) (K := K) (X := X) //
      R.1.weightBlock w = brauerBlock iota hinj bs (D.reduce (iota := iota) d)} = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hWtSub, ⟨⟨T.atOne d, COne.block_atOne d⟩⟩⟩
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

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedDefectZeroCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
