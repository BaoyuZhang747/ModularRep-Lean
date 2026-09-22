import ModularRep.PaperProofs.TypeBConlonJordanSourceInstantiation
import ModularRep.PaperProofs.TypeBPhysicalDecompositionAction
import ModularRep.PaperProofs.TypeBPhysicalBlockAction
import ModularRep.PaperProofs.TypeBFLZJordanSourceBinding

/-!
# Lemma 4.2 with the specified tensor/field block action

Every primitive block acts by the explicit weighted group algebra
automorphism. Brauer-block transport and the same ordinary specified selector
are equivariant by checked deductions. The consumer has no independent
primitive-block action, ordinary/Brauer equivariance or nonempty premise.
All published Jordan/core/series/integral/scalar inputs remain explicit.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonPhysicalActionInstantiation

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

/-- Canonical action, installed explicitly before the actual stabilizer certificates. -/
@[instance_reducible]
def actualBlockAction {k M E : Type} [Field k] [Group M] [Finite M] [Group E]
    (G0 : Subgroup M) [G0.Normal] (field : E →* MulAut M)
    (hinvariant : TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant G0 field) :
    MulAction (ActingGroup (k := k) G0 field hinvariant) (LiteralPrimitiveBlock k M) :=
  TypeBPhysicalBlockAction.blockAction G0 field hinvariant
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
variable (Msys : ModularSystem ell K O k)
variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)

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
theorem specialClifford_lemma_4_3_physical_action_instantiated
    (productFormula : BrauerLinearTensorProductFormula iota)
    [Finite (jordan.toEquation34 zero descent).rationalSeriesSource.Basic]
    (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)
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
    (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :
    let _ : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) :=
      (jordan.toEquation34 zero descent).ordinary_roots
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
        actualBlockAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
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
    IsPHypoelementary 2 J ∧
      Nonempty
        ((Representation.ofMulAction ℤ J
          (BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b)).Equiv
          (Representation.ofMulAction ℤ J
            (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
        BlockFibre (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) b,
        ∀ (j : J) phi, e (j • phi) = j • e phi := by
  dsimp only
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) :=
    (jordan.toEquation34 zero descent).ordinary_roots
  letI : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
      actualBlockAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  intro conlon burnside
  have hBrBlock := TypeBPhysicalBlockAction.brauerBlockEquivariant
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    iota productFormula hinj blocks
  have hOrdBlock := TypeBPhysicalDecompositionAction.ordinaryBlock_equivariant_of_brauer
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    D Msys iota hcompat hinj productFormula liftCompatible blocks ordinary hBrBlock
  exact TypeBConlonJordanSourceInstantiation.specialClifford_lemma_4_3_jordan_source_instantiated
    parameters N fs D Msys iota hcompat hinj scope choice
    primary source values jordan zero descent inputs blocks ordinary C U literal23
    productFormula hseries hOrdBlock hBrBlock
    liftCompatible eq35 liftTrivial tensorLabel tensor_character tensor_parameter
    b conlon burnside

end ModularRep.PaperProofs.TypeBConlonPhysicalActionInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
