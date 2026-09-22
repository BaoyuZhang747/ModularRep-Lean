import ModularRep.PaperProofs.TypeBConlonLiteralProfileInstantiation
import ModularRep.PaperProofs.TypeBFLZOccurringCharacterSource

/-!
# Lemma 4.2 from the occurring-component character source

The same literal profile Conlon endpoint is specialized to the actual
occurring-component source over AlgebraicClosure K. The source provider
restricts literal full labels using canonical zero labels, realizes the
published occurring characters, and descends the actual centralizer
characters to the prescribed characteristic-zero field K.

The primary-component interpretation, zero-symbol uniqueness and actual
centralizer descent are explicit narrow inputs. This consumer adds no
source field, label map, action law or target premise. It retains the
same derived literal source in S, the specified block classifier, the full
union and the literal per-series integral certificate, together with
every scalar, tensor, field, root and actual stabilizer hypothesis.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonOccurringSourceInstantiation

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
variable (primary : TypeBFLZPrimarySource.PrimarySource parameters scope)
variable (source : TypeBFLZOccurringCharacterSource.OccurringCharacterSource
  (K := K) parameters scope primary)
variable (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
variable (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
  (F := F) (K := K) (p := p) (n := n))

variable (inputs : TypeBFLZLiteralProfileModel.RemovalInputs)
local instance actualFullPairAction : MulAction (CSp F n) (FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :=
  TypeBFLZCentralizerConjugacy.fullPairAction (source.toLiteralSource zero descent dualRoots).unipotent
    (labelStable TypeBFLZLiteralProfileModel.Psi (source.toLiteralSource zero descent dualRoots).unipotent (source.toLiteralSource zero descent dualRoots).label (source.toLiteralSource zero descent dualRoots).square)
variable (S : Equation34Source (ell := ell) (source.toLiteralSource zero descent dualRoots).unipotent)
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
  (source.toLiteralSource zero descent dualRoots).unipotent (source.toLiteralSource zero descent dualRoots).label S (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks)

variable (U : TypeBFLZBlockUnionSplitting.BlockUnionCertificate S
  (CoreFamily (coreByClass TypeBFLZLiteralProfileModel.Psi TypeBFLZLiteralProfileModel.RawCore
    (TypeBFLZLiteralScope.takeCore parameters scope inputs)))
  (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks
  (TypeBFLZProfileCoreSource.toTheorem63Source TypeBFLZLiteralProfileModel.Psi
    TypeBFLZLiteralProfileModel.RawCore (TypeBFLZLiteralScope.takeCore parameters scope inputs)
    (source.toLiteralSource zero descent dualRoots).unipotent (source.toLiteralSource zero descent dualRoots).label S
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock iota blocks C))
variable (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
  Msys iota hinj S blocks ordinary hcompat)

include U literal23 in
/-- The Conlon endpoint uses the actual profile label/extractor and both
constructed pair actions, with the SAME specified block and integral data. -/
theorem specialClifford_lemma_4_3_occurring_source_instantiated
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
      CharacterPair F K p ell n (source.toLiteralSource zero descent dualRoots).unipotent → CharacterPair F K p ell n (source.toLiteralSource zero descent dualRoots).unipotent)
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
  exact TypeBConlonLiteralProfileInstantiation.specialClifford_lemma_4_3_literal_profile_instantiated
    parameters N fs D Msys iota hcompat hinj scope dualRoots
    (source.toLiteralSource zero descent dualRoots) inputs
    S blocks ordinary C U literal23 productFormula hseries hOrdBlock hBrBlock
    liftCompatible eq35 liftTrivial tensorLabel tensor_character tensor_parameter
    b brauer_nonempty conlon burnside

end ModularRep.PaperProofs.TypeBConlonOccurringSourceInstantiation




/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
