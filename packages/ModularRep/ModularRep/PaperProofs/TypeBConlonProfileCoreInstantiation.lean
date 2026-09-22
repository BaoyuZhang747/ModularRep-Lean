import ModularRep.PaperProofs.TypeBFLZProfileCoreSource
import ModularRep.PaperProofs.TypeBConlonPhysicalSourceInstantiation
import ModularRep.PaperProofs.TypeBConlonBlockFLZSplitting
import ModularRep.PaperProofs.TypeBFLZCentralizerConjugacy
import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting
import ModularRep.PaperProofs.TypeBFLZLiteralIntegralSeries

/-!
# Lemma 4.2 with profile cores and constructed conjugation actions

The exact profile-label character-value square constructs unipotent
stability and the action on actual centralizer-character pairs. Core pairs
use the range of the SAME profile core operator with its proved conjugation
action. The narrower FLZ 6.3 certificate states only classification and
membership on these pairs. Its adapter supplies the derived extractor.

The SAME specified ordinary selector, full-union certificate and literal
individual-series integral certificate feed the frozen Conlon deduction.
No core action, arbitrary extractor, independent stability or blockwise
matching is a premise. The literal partition/odd-defect-symbol interpretation
of Psi/RawCore/takeCore, actual unipotent labelling and published-source
realizations remain explicit obligations.
-/
noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonProfileCoreInstantiation

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
variable (unipotent : UnipotentPredicate F K p n)
/-- Exact profile-label data, bundled so the constructed action's instance
parameters can be inferred from the actual unipotent carrier. This is not
a published-model realization: literal Psi and the label interpretation
remain explicit obligations. No action or stability field is supplied. -/
class CharacterLabels where
  Psi : Profile F → Type
  label : ∀ s : TypeBFLZLabelSource.SemisimpleParameter F p n,
    Psi (semisimpleProfile s) ≃
      {chi : Irr K (TypeBFLZLabelSource.parameterCentralizer F p n s) // unipotent s chi}
  square : CharacterSquare Psi unipotent label

variable [labels : CharacterLabels unipotent]
variable (RawCore : Profile F → Type)
variable (takeCore : ∀ profile, labels.Psi profile → RawCore profile)
local instance actualFullPairAction : MulAction (CSp F n) (FullCharacterPair F K p n unipotent) :=
  TypeBFLZCentralizerConjugacy.fullPairAction unipotent
    (labelStable labels.Psi unipotent labels.label labels.square)
variable (S : Equation34Source (ell := ell) unipotent)
local instance actualCorePairAction : MulAction (CSp F n)
    (BlockPair F p ell n (CoreFamily (coreByClass labels.Psi RawCore takeCore))) :=
  corePairAction (coreByClass labels.Psi RawCore takeCore)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
  Msys iota hinj blocks (ordinaryRoots := S.ordinary_roots))
variable (C : TypeBFLZProfileCoreSource.Theorem63Certificate labels.Psi RawCore takeCore
  unipotent labels.label S (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks)

variable (U : TypeBFLZBlockUnionSplitting.BlockUnionCertificate S
  (CoreFamily (coreByClass labels.Psi RawCore takeCore))
  (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks
  (TypeBFLZProfileCoreSource.toTheorem63Source labels.Psi RawCore takeCore unipotent labels.label S
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks C))
variable (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
  Msys iota hinj S blocks ordinary hcompat)

include U literal23 in
/-- The Conlon endpoint uses the actual profile label/extractor and both
constructed pair actions, with the SAME specified block and integral data. -/
theorem specialClifford_lemma_4_3_profile_core_instantiated
    (productFormula : BrauerLinearTensorProductFormula iota)
    [Finite S.rationalSeriesSource.Basic]
    (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        S.rationalSeriesSource.selectedSeries)
    (hOrdBlock : TypeCConformalActionAdapter.OrdinaryBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock)
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
      CharacterPair F K p ell n unipotent → CharacterPair F K p ell n unipotent)
    (tensor_character : ∀ c l,
      S.familyCharacter (tensorLabel c l) =
        @SMul.smul (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) S.rationalSeriesSource.Basic
          (ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
            (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries
            hseries).toSMul (SemidirectProduct.inl c) (S.familyCharacter l))
    (tensor_parameter : ∀ c l,
      (tensorLabel c l).1.1 = scalar F n
        (equation35Scalar (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs) D eq35 liftTrivial c)⁻¹ * l.1.1)
    (b : LiteralPrimitiveBlock k (SpecialClifford n F))
    (brauer_nonempty : Nonempty
      (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))
    (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) b))
    (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) b)) :
    let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (OrdinarySeriesCarrier (S.rationalSeriesSource.selectedSeries)) :=
      ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (S.rationalSeriesSource.selectedSeries) hseries
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (IBr iota) :=
      brauerCharacterAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
    let _ : MulAction J (BlockFibre (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock) b) := TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (S.rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock b
      hseries hOrdBlock
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) := brauerBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) b hBrBlock
    IsPHypoelementary 2 J ∧
      Nonempty
        ((Representation.ofMulAction ℤ J
          (BlockFibre (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock) b)).Equiv
          (Representation.ofMulAction ℤ J
            (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
        BlockFibre (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock) b,
        ∀ (j : J) phi, e (j • phi) = j • e phi := by
  letI : Fact (TypeBFLZCentralizerConjugacy.UnipotentStable unipotent) :=
    ⟨labelStable labels.Psi unipotent labels.label labels.square⟩
  exact TypeBConlonPhysicalSourceInstantiation.specialClifford_lemma_4_3_physical_source_instantiated
    parameters N fs D Msys iota hcompat hinj unipotent S
    (CoreFamily (coreByClass labels.Psi RawCore takeCore)) blocks ordinary
    (TypeBFLZProfileCoreSource.toTheorem63Source labels.Psi RawCore takeCore unipotent labels.label S
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks C)
    U literal23 productFormula hseries hOrdBlock hBrBlock liftCompatible eq35 liftTrivial
    tensorLabel tensor_character tensor_parameter b brauer_nonempty conlon burnside

end ModularRep.PaperProofs.TypeBConlonProfileCoreInstantiation



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
