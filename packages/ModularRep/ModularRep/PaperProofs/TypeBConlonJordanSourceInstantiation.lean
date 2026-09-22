import ModularRep.PaperProofs.TypeBConlonOccurringSourceInstantiation
import ModularRep.PaperProofs.TypeBFLZJordanSourceBinding

/-!
# Lemma 4.2 from the same cyclotomic Jordan assignment

The independent Equation (3.4) source is replaced by the actual occurring
pair-orbit Jordan assignment in one prescribed cyclotomic value field. Its
derived ordinary characters, rational series and ordinary-root guard are
used in every specified block, full-union and integral-series certificate.

The Brauer fibre is nonempty by the SAME specified ordinary-block source:
each primitive block has an ordinary preimage and a nonzero decomposition
constituent in that block. No nonemptiness callback or new source field is
introduced. All scalar, tensor, field, modular-system and stabilizer
hypotheses of the checked Conlon deduction remain explicit.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonJordanSourceInstantiation

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
open TypeBFLZCoreProfileConjugacy TypeBFLZCorePairConjugacy
open TypeBFLZCoreExtractionBinding

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)
variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable [Finite (TensorCharacters (k := k) (SpinSubgroup n F N))]
variable [Finite (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
  (field_spinSubgroup_map n F fs))]
variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable [MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
  (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable (Msys : ModularSystem ell K O k)
variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)

/-- Every actual primitive block has a Brauer constituent, using the SAME
specified ordinary selector and its nonzero decomposition support. -/
theorem brauerFibre_nonempty
    (blocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
    (ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)))
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
      Msys iota hinj blocks (ordinaryRoots := ordinaryRoots))
    (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :
    Nonempty (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) := by
  obtain ⟨chi, hchi⟩ :=
    (ordinary.physical (ordinaryRoots := ordinaryRoots)).ordinaryBlock_surjective b
  obtain ⟨phi, hphi⟩ :=
    ((ordinary.physical (ordinaryRoots := ordinaryRoots)).support_nonempty_and_sound chi).1
  have hs :=
    ((ordinary.physical (ordinaryRoots := ordinaryRoots)).support_nonempty_and_sound chi).2
      phi hphi
  have heq : literalBrauerBlock iota hinj blocks phi =
      irreducibleBrauerCharacterBlock iota hinj blocks phi := by
    apply Subtype.ext
    rfl
  exact ⟨⟨phi, heq.symm.trans (hs.trans hchi)⟩⟩

variable (scope : Applicability p ell n)
variable (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)
variable (primary : TypeBFLZPrimarySource.PrimarySource parameters scope)
variable (source : TypeBFLZOccurringCharacterSource.OccurringCharacterSource
  (K := K) parameters scope primary)
variable (values : TypeBFLZJordanSourceBinding.JordanValues source)
variable (jordan : TypeBFLZJordanSourceBinding.JordanCertificate source choice values)
variable (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
variable (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
  (F := F) (K := K) (p := p) (n := n))

variable (inputs : TypeBFLZLiteralProfileModel.RemovalInputs)
local instance actualFullPairAction
    (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n))) :
    MulAction (CSp F n)
      (FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :=
  TypeBFLZCentralizerConjugacy.fullPairAction
    (source.toLiteralSource zero descent dualRoots).unipotent
    (source.toLiteralSource zero descent dualRoots).stable
local instance actualCorePairAction : MulAction (CSp F n)
    (BlockPair F p ell n (CoreFamily (coreByClass TypeBFLZLiteralProfileModel.Psi
      TypeBFLZLiteralProfileModel.RawCore
      (TypeBFLZLiteralScope.takeCore parameters scope inputs)))) :=
  corePairAction (coreByClass TypeBFLZLiteralProfileModel.Psi TypeBFLZLiteralProfileModel.RawCore
    (TypeBFLZLiteralScope.takeCore parameters scope inputs))
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
  Msys iota hinj blocks (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots))
variable (C : TypeBFLZProfileCoreSource.Theorem63Certificate TypeBFLZLiteralProfileModel.Psi
  TypeBFLZLiteralProfileModel.RawCore (TypeBFLZLiteralScope.takeCore parameters scope inputs)
  (source.toLiteralSource zero descent choice.dualRoots).unipotent (source.toLiteralSource zero descent choice.dualRoots).label (jordan.toEquation34 zero descent) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock iota blocks)

variable (U : TypeBFLZBlockUnionSplitting.BlockUnionCertificate (jordan.toEquation34 zero descent)
  (CoreFamily (coreByClass TypeBFLZLiteralProfileModel.Psi TypeBFLZLiteralProfileModel.RawCore
    (TypeBFLZLiteralScope.takeCore parameters scope inputs)))
  (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock iota blocks
  (TypeBFLZProfileCoreSource.toTheorem63Source TypeBFLZLiteralProfileModel.Psi
    TypeBFLZLiteralProfileModel.RawCore (TypeBFLZLiteralScope.takeCore parameters scope inputs)
    (source.toLiteralSource zero descent choice.dualRoots).unipotent (source.toLiteralSource zero descent choice.dualRoots).label (jordan.toEquation34 zero descent)
    (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock iota blocks C))
variable (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
  Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary hcompat)

include U literal23 in
/-- The Conlon endpoint uses the actual profile label/extractor and both
constructed pair actions, with the SAME specified block and integral data. -/
theorem specialClifford_lemma_4_3_jordan_source_instantiated
    (productFormula : BrauerLinearTensorProductFormula iota)
    [Finite (jordan.toEquation34 zero descent).rationalSeriesSource.Basic]
    (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)
    (hOrdBlock : TypeCConformalActionAdapter.OrdinaryBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock)
    (hBrBlock : TypeCConformalActionAdapter.BrauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks))
    (liftCompatible : OrdinaryLiftReductionCompatible (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D iota)
    (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))
    (liftTrivial : ∀ c : TensorCharacters (k := k) (SpinSubgroup n F N),
      TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
        (G0 := SpinSubgroup n F N) (field := fs.action)
        (hinvariant := field_spinSubgroup_map n F fs) D c ∈
          linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))
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
    (b : LiteralPrimitiveBlock k (SpecialClifford n F))
    (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) b))
    (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) b)) :
    let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (OrdinarySeriesCarrier ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)) :=
      ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) hseries
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (IBr iota) :=
      brauerCharacterAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
    let _ : MulAction J (BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b) := TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock b
      hseries hOrdBlock
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) := brauerBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) b hBrBlock
    IsPHypoelementary 2 J ∧
      Nonempty
        ((Representation.ofMulAction ℤ J
          (BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b)).Equiv
          (Representation.ofMulAction ℤ J
            (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
        BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b,
        ∀ (j : J) phi, e (j • phi) = j • e phi := by
  exact TypeBConlonOccurringSourceInstantiation.specialClifford_lemma_4_3_occurring_source_instantiated
    parameters N fs D Msys iota hcompat hinj scope choice.dualRoots
    primary source zero descent inputs
    (jordan.toEquation34 zero descent) blocks ordinary C U literal23
    productFormula hseries hOrdBlock hBrBlock
    liftCompatible eq35 liftTrivial tensorLabel tensor_character tensor_parameter
    b (brauerFibre_nonempty Msys iota hinj blocks
      (jordan.toEquation34 zero descent).ordinary_roots ordinary b) conlon burnside

end ModularRep.PaperProofs.TypeBConlonJordanSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
