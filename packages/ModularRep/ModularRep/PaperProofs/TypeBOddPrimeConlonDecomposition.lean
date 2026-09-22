import ModularRep.PaperProofs.TypeBConlonBroueMichelInstantiation

/-!
# The literal block decomposition maps in `lem:type-b-conlon-block`

The September 8 statement names the restricted decomposition map itself.
The accepted Conlon endpoints already construct its lattice equivalence,
but retain only existence of a lattice equivalence in their public results.
Here the same individual FLZ Theorem 2.3 packet is aggregated and restricted
with the specified ordinary-block support. Its exact generator and full K0
equations are retained in the conclusion, as is equality of the underlying
lattice map with that specific restriction.

Minimal inputs are the existing literal rational-series/individual integral
certificate, specified ordinary blocks and stable reduction, and the actual
tensor/field or diagonal/field actions with separate series stability. No
global basic set, blockwise equivalence, naturality, hypoelementarity or
bijection is an external input. The accepted scalar/Conlon deduction is
reused separately by the final two-group application; this supporting file
does not itself identify the Spin outer model with Aut(G)_B/Inn(G).

Source grades and locators are unchanged: FLZ Theorem 2.3 p.537 (E2),
Navarro 2.9 p.23 and specified decomposition support (E1), FLZ Lemma 3.6
and Section 3.5 pp.545--546 (E2/E1). The algebraic centre component orders
are one for special Clifford and two for Spin. These are distinct from the
coefficient prime two in the later Conlon bridge.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBOddPrimeConlonDecomposition

open ModularRep BlockFibreRestriction DecompositionBasicSetBridge
open ExactGrothendieckGroup FDRepSimpleClassKZero IntegralBasicSetBridge
open OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesSplitting
open TypeBSpecialCliffordActionAdapter TypeBSpecialCliffordActionSplitting
open OddConformalProposition311Relative TypeBOddPrimesProposition44Relative
open TypeBFLZLabelSource (UnipotentPredicate FullCharacterPair SourceIndex)
open TypeBFLZLabelSplittingSource

section SpecialClifford

variable {p ell f n : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (fs : FieldActionSource n F p f parameters N)
  (D : OrdinaryReductionEquiv (k := k) (K := K) (SpinSubgroup n F N)
    fs.action (field_spinSubgroup_map n F fs))
  [Fintype (SourceIndex F p ell n)]
  [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
  (Msys : ModularSystem ell K O k)
  (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  {unipotent : UnipotentPredicate F K p n}
  [MulAction (TypeBConformalDualCarriers.CSp F n)
    (FullCharacterPair F K p n unipotent)]
  (S : Equation34Source (ell := ell) unipotent)
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
  (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
    Msys iota hinj blocks (ordinaryRoots := S.ordinary_roots))
  (union : TypeBSpecialCliffordBroueMichelSource.BlockUnionCertificate
    Msys iota hinj S blocks ordinary)
  (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
    Msys iota hinj S blocks ordinary hcompat)

/-- The SAME chosen individual source packet as in the accepted BM endpoint. -/
def specialCliffordSeriesData :=
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := S.ordinary_roots
  let source23 := TypeBSpecialCliffordBroueMichelSource.toTheorem23Certificate
    Msys iota hinj S blocks ordinary union hcompat literal23
  Classical.choice (source23.applies
    (TypeBConlonBlockFLZSplitting.theorem23Hypotheses S.hypotheses))

/-- The literal block restriction of the derived integral basic set. -/
def specialCliffordBlockBasicSet (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :=
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := S.ordinary_roots
  let bi := TypeBSpecialCliffordBroueMichelSource.blockSeries
    Msys iota hinj S blocks ordinary union
  let data := specialCliffordSeriesData Msys iota hinj hcompat S blocks ordinary union literal23
  let basic := data.globalBasicSet Msys iota hcompat hinj S.rationalSeriesSource blocks bi
  let blockOf := ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock
  let hd := blockDiagonalLinearEquiv_of_generator_support blockOf
    (irreducibleBrauerCharacterBlock iota hinj blocks) basic.linearEquiv
    (TypeBOrdinaryBlockSplitting.forwardSupport Msys iota hinj blocks ordinary hcompat
      S.rationalSeriesSource bi data)
  restrictRestrictedIntegralBasicSet basic.toRestrictedIntegralBasicSet blockOf
    (irreducibleBrauerCharacterBlock iota hinj blocks) hd b

/-- On the actual special Clifford stabilizer, the constructed lattice map
is exactly the block restriction of stable decomposition, on every vector
and in particular on every selected ordinary-character generator. -/
theorem specialClifford_decomposition_lattice
    (productFormula : BrauerLinearTensorProductFormula iota)
    (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
      S.rationalSeriesSource.selectedSeries)
    (liftCompatible : OrdinaryLiftReductionCompatible (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs) D iota)
    (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :
    let _ : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := S.ordinary_roots
    let _ := TypeBConlonPhysicalActionInstantiation.actualBlockAction (k := k)
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let _ := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries hseries
    let _ := brauerCharacterAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) iota productFormula
    let hBr := TypeBPhysicalBlockAction.brauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      iota productFormula hinj blocks
    let hOrd := TypeBPhysicalDecompositionAction.ordinaryBlock_equivariant_of_brauer
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      D Msys iota hcompat hinj productFormula liftCompatible blocks ordinary hBr
    let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs)) b
    let blockOf := ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock
    let _ : MulAction J (BlockFibre blockOf b) :=
      TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        S.rationalSeriesSource.selectedSeries
        (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock b hseries hOrd
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      brauerBlockFibreAction (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs) iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks) b hBr
    let restricted := specialCliffordBlockBasicSet
      Msys iota hinj hcompat S blocks ordinary union literal23 b
    ∃ dB : (Representation.ofMulAction ℤ J (BlockFibre blockOf b)).Equiv
        (Representation.ofMulAction ℤ J
          (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b)),
      dB.toLinearEquiv = restricted.linearEquiv ∧
      (∀ v, labelledSimpleClassKZero restricted.modularLabel (dB.toLinearEquiv v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero restricted.ordinaryLabel v)) ∧
      (∀ x : BlockFibre blockOf b,
        labelledSimpleClassKZero restricted.modularLabel
          (dB.toLinearEquiv (MonoidAlgebra.single x 1)) =
        decompositionMapOfStableReduction Msys iota hcompat
          (simpleClassToFDRepKZeroGenerator (restricted.ordinaryLabel x))) := by
  classical
  dsimp only
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := S.ordinary_roots
  letI := TypeBConlonPhysicalActionInstantiation.actualBlockAction (k := k)
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) iota productFormula
  let hBr := TypeBPhysicalBlockAction.brauerBlockEquivariant
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    iota productFormula hinj blocks
  let hOrd := TypeBPhysicalDecompositionAction.ordinaryBlock_equivariant_of_brauer
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    D Msys iota hcompat hinj productFormula liftCompatible blocks ordinary hBr
  let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N)
    fs.action (field_spinSubgroup_map n F fs)) b
  let blockOf := ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock
  letI : MulAction J (BlockFibre blockOf b) :=
    TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
      S.rationalSeriesSource.selectedSeries
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock b hseries hOrd
  letI : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
    brauerBlockFibreAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) b hBr
  let bi := TypeBSpecialCliffordBroueMichelSource.blockSeries
    Msys iota hinj S blocks ordinary union
  let data := specialCliffordSeriesData Msys iota hinj hcompat S blocks ordinary union literal23
  let basic := data.globalBasicSet Msys iota hcompat hinj S.rationalSeriesSource blocks bi
  let hd := blockDiagonalLinearEquiv_of_generator_support blockOf
    (irreducibleBrauerCharacterBlock iota hinj blocks) basic.linearEquiv
    (TypeBOrdinaryBlockSplitting.forwardSupport Msys iota hinj blocks ordinary hcompat
      S.rationalSeriesSource bi data)
  let ambient := TypeBSpecialCliffordActionSplitting.labelledKZeroActionData
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D Msys iota
    hcompat hinj productFormula S.rationalSeriesSource blocks bi data hseries
  let actions := restrictLabelledKZeroActionDataToSubgroup basic ambient J
    (fun _ _ => rfl) (fun _ _ => rfl)
  have natural := decompositionNatural_restrict_subgroup basic ambient
    (TypeBSpecialCliffordActionSplitting.decompositionNatural (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs) D Msys iota hcompat
      productFormula liftCompatible) J (fun _ _ => rfl) (fun _ _ => rfl)
  let restricted := specialCliffordBlockBasicSet
    Msys iota hinj hcompat S blocks ordinary union literal23 b
  have matrix : MatrixEquivariant (A := J) restricted.linearEquiv.toLinearMap :=
    matrixEquivariant_restrictBlock_of_kZero_naturality
      basic.toRestrictedIntegralBasicSet hd actions natural (fun _ _ => rfl) (fun _ _ => rfl)
  let dB := permutationLatticeEquiv restricted.linearEquiv matrix
  refine ⟨dB, rfl, ?_, ?_⟩
  · exact restricted.restricts_decomposition
  · intro x
    change labelledSimpleClassKZero restricted.modularLabel
        (restricted.linearEquiv (MonoidAlgebra.single x 1)) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator (restricted.ordinaryLabel x))
    simpa only [labelledSimpleClassKZero_single] using
      restricted.restricts_decomposition (MonoidAlgebra.single x 1)

end SpecialClifford


namespace SourceInstantiation

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero IntegralBasicSetBridge OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesSplitting
open TypeBFLZLabelSource (UnipotentPredicate FullCharacterPair AdmissibleParameter BlockPair
  CharacterPair SourceIndex Applicability)
open TypeBFLZLabelSplittingSource
open TypeBConlonBlockRelative OddConformalProposition311Relative
open TypeBOddPrimesProposition44Relative
open TypeBConlonBlockSourceInstantiation ConlonBasicSet
open TypeBConlonPhysicalActionInstantiation
open TypeBSpecialCliffordActionSplitting

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)
variable (D : OrdinaryReductionEquiv (k := k) (K := K) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable [Finite (TensorCharacters (k := k) (SpinSubgroup n F N))]
variable [Finite (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
  (field_spinSubgroup_map n F fs))]
variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable (Msys : ModularSystem ell K O k)
variable (scope : Applicability p ell n)
variable (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)

variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
variable (primary : TypeBFLZPrimarySource.PrimarySource parameters scope)
variable (source : TypeBFLZOccurringCharacterSource.OccurringCharacterSource
  (K := K) parameters scope primary)
variable (values : TypeBFLZJordanSourceBinding.JordanValues source)
variable (jordan : TypeBFLZJordanSourceBinding.JordanCertificate source choice values)
variable (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
variable (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
  (F := F) (K := K) (p := p) (n := n))

local instance actualFullPairAction
    (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n))) :
    MulAction (CSp F n)
      (FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :=
  TypeBFLZCentralizerConjugacy.fullPairAction
    (source.toLiteralSource zero descent dualRoots).unipotent
    (source.toLiteralSource zero descent dualRoots).stable
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
  Msys iota hinj blocks (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots))
variable (union : TypeBSpecialCliffordBroueMichelSource.BlockUnionCertificate
  Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary)
variable (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
  Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary hcompat)


/-- The revised special-Clifford manuscript deduction on the SAME modular
root, Jordan tuple, specified block and individual integral source packet.
The accepted scalar and Conlon proof supplies hypoelementarity and the
bijection. The named lattice map is the literal restricted decomposition,
whose full-vector and ordinary-generator equations are retained here.
This source-conditioned theorem adds no external premise to the accepted
special-Clifford application. -/
theorem specialClifford_revised_conlon_block :
    let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
    let hinj : IrreducibleBrauerCharacterInjectivity iota := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftTrivial := TypeBModularLinearCharacterLift.liftTrivial iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    ∀
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (primary : TypeBFLZPrimarySource.PrimarySource parameters scope)
    (source : TypeBFLZOccurringCharacterSource.OccurringCharacterSource
  (K := K) parameters scope primary)
    (values : TypeBFLZJordanSourceBinding.JordanValues source)
    (jordan : TypeBFLZJordanSourceBinding.JordanCertificate source choice values)
    (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
    (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
  (F := F) (K := K) (p := p) (n := n))

    (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
  Msys iota hinj blocks (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots))
    (union : TypeBSpecialCliffordBroueMichelSource.BlockUnionCertificate
  Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary)
    (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
  Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary hcompat)

    (productFormula : BrauerLinearTensorProductFormula iota)
    [Finite (jordan.toEquation34 zero descent).rationalSeriesSource.Basic]
    (tensorStable : TypeCConformalActionAdapter.OrdinarySeriesTensorStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)
    (fieldStable : TypeCConformalActionAdapter.OrdinarySeriesFieldStable (K := K)
      fs.action (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries),
    let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
      (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
      tensorStable fieldStable
    ∀ (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))
    (tensorLabel : TensorCharacters (k := k) (SpinSubgroup n F N) →
      CharacterPair F K p ell n (source.toLiteralSource zero descent choice.dualRoots).unipotent → CharacterPair F K p ell n (source.toLiteralSource zero descent choice.dualRoots).unipotent)
    (tensor_character : ∀ c l,
      (jordan.toEquation34 zero descent).familyCharacter (tensorLabel c l) =
        @SMul.smul (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (jordan.toEquation34 zero descent).rationalSeriesSource.Basic
          (ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
            (field_spinSubgroup_map n F fs) D (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
            hseries).toSMul (SemidirectProduct.inl c) ((jordan.toEquation34 zero descent).familyCharacter l))
    (tensor_parameter : ∀ c l,
      (tensorLabel c l).1.1 = scalar F n
        (equation35Scalar (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs) D eq35 liftTrivial c)⁻¹ * l.1.1)
    (b : LiteralPrimitiveBlock k (SpecialClifford n F)) ,
    let _ : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) :=
      (jordan.toEquation34 zero descent).ordinary_roots
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
        actualBlockAction (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    ∀
    (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) b))
    (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) b)),
    let hBrBlock := TypeBPhysicalBlockAction.brauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      iota productFormula hinj blocks
    let hOrdBlock := TypeBPhysicalDecompositionAction.ordinaryBlock_equivariant_of_brauer
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      D Msys iota hcompat hinj productFormula liftCompatible blocks ordinary hBrBlock
    let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (OrdinarySeriesCarrier ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)) :=
      ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) hseries
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (IBr iota) :=
      brauerCharacterAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
    let _ : MulAction J (BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b) := TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock b
      hseries hOrdBlock
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) := brauerBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) b hBrBlock
    let restricted := specialCliffordBlockBasicSet Msys iota hinj hcompat
      (jordan.toEquation34 zero descent) blocks ordinary union literal23 b
    IsPHypoelementary 2 J ∧
      (∃ dB : ((Representation.ofMulAction ℤ J
          (BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b)).Equiv
          (Representation.ofMulAction ℤ J
            (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))),
        dB.toLinearEquiv = restricted.linearEquiv ∧
        (∀ v, labelledSimpleClassKZero restricted.modularLabel (dB.toLinearEquiv v) =
          decompositionMapOfStableReduction Msys iota hcompat
            (labelledSimpleClassKZero restricted.ordinaryLabel v)) ∧
        (∀ x : BlockFibre
            (ordinarySeriesBlockMap (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
              (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b,
          labelledSimpleClassKZero restricted.modularLabel
              (dB.toLinearEquiv (MonoidAlgebra.single x 1)) =
            decompositionMapOfStableReduction Msys iota hcompat
              (simpleClassToFDRepKZeroGenerator (restricted.ordinaryLabel x)))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
        BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b,
        ∀ (j : J) phi, e (j • phi) = j • e phi :=
  let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
  let hinj : IrreducibleBrauerCharacterInjectivity iota := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let liftTrivial := TypeBModularLinearCharacterLift.liftTrivial iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  fun hcompat primary source values jordan zero descent blocks ordinary union literal23 productFormula finiteBasic tensorStable fieldStable =>
  let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
      (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
      tensorStable fieldStable
  fun eq35 tensorLabel tensor_character tensor_parameter b =>
  by
    dsimp only
    letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) :=
      (jordan.toEquation34 zero descent).ordinary_roots
    letI := actualBlockAction (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    letI := finiteBasic
    intro conlon burnside
    have old := TypeBConlonBroueMichelInstantiation.specialClifford_lemma_4_3_broue_michel_instantiated
      (parameters := parameters) (N := N) (fs := fs) (Msys := Msys)
      (scope := scope) (choice := choice)
      hcompat primary source values jordan zero descent blocks ordinary union literal23
      productFormula hseries eq35 tensorLabel tensor_character tensor_parameter b conlon burnside
    have exactMap := specialClifford_decomposition_lattice
      (fs := fs) (D := D) (Msys := Msys) (iota := iota) (hinj := hinj)
      (hcompat := hcompat) (S := jordan.toEquation34 zero descent)
      (blocks := blocks) (ordinary := ordinary) (union := union) (literal23 := literal23)
      productFormula hseries liftCompatible b
    obtain ⟨dB, hmap, hred, hgen⟩ := exactMap
    exact ⟨old.1, ⟨dB, hmap, hred, hgen⟩, old.2.2⟩

end SourceInstantiation
end ModularRep.PaperProofs.TypeBOddPrimeConlonDecomposition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
