import ModularRep.PaperProofs.TypeBConlonProfileCoreInstantiation
import ModularRep.PaperProofs.TypeBFLZLiteralProfileModel
import ModularRep.PaperProofs.TypeBFLZLiteralScope
import ModularRep.PaperProofs.TypeBFLZLiteralCharacterSource

/-!
# Lemma 4.2 on the literal polynomial/partition/symbol profile model

The profile label family, raw core carrier and core operator are the
checked literal constructions. A guarded source injects those labels into
actual centralizer characters with their pointwise conjugation square.
Its image predicate and derived label equivalence construct the old packet
and the same full-pair action; no free unipotent predicate or label
equivalence remains. Core pairs use the constructed class-indexed action.

The arithmetic scope is derived from the same field parameters and S's
applicability record, without extra numerical guards. The specified
ordinary selector, prescribed roots, same full-union and
individual integral-series certificates, scalar/tensor/field data and
actual block stabilizer are retained. The proof is a direct specialization
of the frozen Conlon deduction. Source realization remains explicit; no
BAW/iBAW or numbered target is assumed and no such window is accepted
merely by this conditional literal-model specialization.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonLiteralProfileInstantiation

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
variable (scope : Applicability p ell n)
variable (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n)))
variable (source : TypeBFLZLiteralCharacterSource.CharacterSource parameters scope dualRoots)

/-- The old packet is derived from the guarded literal injection source;
its predicate is the exact image and its family is the literal profile. -/
def toProfileCharacterLabels :
    TypeBConlonProfileCoreInstantiation.CharacterLabels source.unipotent where
  Psi := TypeBFLZLiteralProfileModel.Psi
  label := source.label
  square := source.square

@[simp]
theorem toProfileCharacterLabels_Psi :
    (toProfileCharacterLabels parameters scope dualRoots source).Psi =
      TypeBFLZLiteralProfileModel.Psi := rfl

@[simp]
theorem toProfileCharacterLabels_label :
    (toProfileCharacterLabels parameters scope dualRoots source).label = source.label := rfl

local instance actualProfileCharacterLabels :
    TypeBConlonProfileCoreInstantiation.CharacterLabels source.unipotent :=
  toProfileCharacterLabels parameters scope dualRoots source

variable (inputs : TypeBFLZLiteralProfileModel.RemovalInputs)
local instance actualFullPairAction : MulAction (CSp F n) (FullCharacterPair F K p n source.unipotent) :=
  TypeBFLZCentralizerConjugacy.fullPairAction source.unipotent
    (labelStable TypeBFLZLiteralProfileModel.Psi source.unipotent source.label source.square)
variable (S : Equation34Source (ell := ell) source.unipotent)
local instance actualCorePairAction : MulAction (CSp F n)
    (BlockPair F p ell n (CoreFamily (coreByClass TypeBFLZLiteralProfileModel.Psi
      TypeBFLZLiteralProfileModel.RawCore
      (TypeBFLZLiteralScope.takeCore parameters scope inputs)))) :=
  corePairAction (coreByClass TypeBFLZLiteralProfileModel.Psi TypeBFLZLiteralProfileModel.RawCore
    (TypeBFLZLiteralScope.takeCore parameters scope inputs))
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
  Msys iota hinj blocks (ordinaryRoots := S.ordinary_roots))
variable (C : TypeBFLZProfileCoreSource.Theorem63Certificate TypeBFLZLiteralProfileModel.Psi
  TypeBFLZLiteralProfileModel.RawCore (TypeBFLZLiteralScope.takeCore parameters scope inputs)
  source.unipotent source.label S (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks)

variable (U : TypeBFLZBlockUnionSplitting.BlockUnionCertificate S
  (CoreFamily (coreByClass TypeBFLZLiteralProfileModel.Psi TypeBFLZLiteralProfileModel.RawCore
    (TypeBFLZLiteralScope.takeCore parameters scope inputs)))
  (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks
  (TypeBFLZProfileCoreSource.toTheorem63Source TypeBFLZLiteralProfileModel.Psi
    TypeBFLZLiteralProfileModel.RawCore (TypeBFLZLiteralScope.takeCore parameters scope inputs)
    source.unipotent source.label S
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks C))
variable (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
  Msys iota hinj S blocks ordinary hcompat)

include U literal23 in
/-- The Conlon endpoint uses the actual profile label/extractor and both
constructed pair actions, with the SAME specified block and integral data. -/
theorem specialClifford_lemma_4_3_literal_profile_instantiated
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
      CharacterPair F K p ell n source.unipotent → CharacterPair F K p ell n source.unipotent)
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
  exact TypeBConlonProfileCoreInstantiation.specialClifford_lemma_4_3_profile_core_instantiated
    parameters N fs D Msys iota hcompat hinj source.unipotent
    TypeBFLZLiteralProfileModel.RawCore (TypeBFLZLiteralScope.takeCore parameters scope inputs)
    S blocks ordinary C U literal23 productFormula hseries hOrdBlock hBrBlock
    liftCompatible eq35 liftTrivial tensorLabel tensor_character tensor_parameter
    b brauer_nonempty conlon burnside

end ModularRep.PaperProofs.TypeBConlonLiteralProfileInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
