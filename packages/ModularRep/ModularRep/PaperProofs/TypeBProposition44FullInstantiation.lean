import ModularRep.PaperProofs.TypeBProposition44BroueMichelInstantiation
import ModularRep.PaperProofs.TypeBSpinConstituentInstantiation
import ModularRep.PaperProofs.TypeBSpinRawWeightSeparationBinding
import ModularRep.PaperProofs.TypeBSpinExtensionInstantiation
import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.PaperProofs.TypeBSpinCoverSource
import ModularRep.PaperProofs.TypeBFullCriterionSplittingSource
import ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding
import ModularRep.PaperProofs.TypeBActualAmbientRootBinding
import ModularRep.PaperProofs.TypeBSpinStructuralCoverBinding

/-!
# The concrete Type B application of the complete published criterion

The same Jordan source supplies the upper correspondence and the lower
constituent deduction. All roots, ordinary linear lifts, radical kernels,
local reductions, Hall products and extension clauses use the same actual
modular system and Clifford norm. The input contains independent published
sources and literal carrier facts. The entire criterion domain is combined
in the proof; no domain packet or desired matching is supplied.

This generic Spin application retains the exceptional-cover exclusion and
all specified block and sufficient ordinary-root guards. Source acceptance
is conditional on the exact published certificates on these carriers.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBProposition44FullInstantiation

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero IntegralBasicSetBridge OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesSplitting
open TypeBFLZLabelSource (UnipotentPredicate FullCharacterPair SemisimpleParameter AdmissibleParameter BlockPair
  CharacterPair SourceIndex Applicability)
open TypeBFLZLabelSplittingSource
open TypeBConlonBlockRelative OddConformalProposition311Relative
open TypeBOddPrimesProposition44Relative
open TypeBConlonBlockSourceInstantiation ConlonBasicSet
open TypeBConlonPhysicalActionInstantiation
open TypeBSpecialCliffordActionSplitting

open OddConlonOrbitAssembly TypeCWeightTensorFieldAction
open TypeBProposition44OrdinaryWeightBinding


open TypeBCriterionHypotheses TypeBCriterionCarrierBindings

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)
variable (Msys : ModularSystem ell K O k) (scope : Applicability p ell n)
variable (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)
local instance cliffordFintype : Fintype (SpecialClifford n F) := Fintype.ofFinite _
local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

section BlockData

variable [finiteUpperBlocks : Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable [finiteLowerBlocks : Fintype (LiteralPrimitiveBlock k (Spin n F N))]
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (blockSource : CharacterWeight.LocalBlockInductionSource
  (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
  (Block := LiteralPrimitiveBlock k (SpecialClifford n F)))
variable (ambientPhysical : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
  blockSource.operations.ambientBlockData.blockIdempotent b = b.val)
variable (spinBlocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.1))
variable (spinBlockSource : CharacterWeight.LocalBlockInductionSource
  (p := ell) (k := k) (K := K) (G := Spin n F N)
  (Block := LiteralPrimitiveBlock k (Spin n F N)))
variable (spinAmbientPhysical : ∀ b : LiteralPrimitiveBlock k (Spin n F N),
  spinBlockSource.operations.ambientBlockData.blockIdempotent b = b.val)

/-- Both primitive block catalogues and both local induction operations
are the same objects used by the source consumers. -/
def blockData : BlockData (ell := ell) (k := k) (K := K) (SpinSubgroup n F N) where
  downstairs := spinBlocks
  upstairs := blocks
  weightDownstairs := spinBlockSource
  weightUpstairs := blockSource
  downstairs_idempotent := spinAmbientPhysical
  upstairs_idempotent := ambientPhysical

end BlockData

/-- The full generic-cover output follows from the independent current
Type B sources. Computed roots and actions are scoped before their
source binders, and the complete criterion input is constructed in the proof. -/
theorem full_criterion_modular_instantiated :
    letI ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) :=
      choice.ordinaryRoots
    letI spinOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
      TypeBSpinJordanRestrictionSource.spinRoots N choice
    let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
    let iotaG := TypeBFLZModularRootBinding.spinRoot Msys choice N
    let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let hinjG := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG
    let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftTrivial := TypeBModularLinearCharacterLift.liftTrivial iota
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let radicalKernel := TypeBProposition44BroueMichelInstantiation.canonicalRadicalKernel parameters N fs iota
    ∀ [finiteTensor : Finite (TensorCharacters (k := k) (SpinSubgroup n F N))],
    ∀ [finiteActing : Finite (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs))],
    ∀ [finiteUpperBlocks : Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))],
    ∀ [finiteLowerBlocks : Fintype (LiteralPrimitiveBlock k (Spin n F N))],
    ∀ (hcompat : StableReductionBrauerCharacterCompatibility Msys iota),
    ∀ (primary : TypeBFLZPrimarySource.PrimarySource parameters scope),
    ∀ (source : TypeBFLZOccurringCharacterSource.OccurringCharacterSource
      (K := K) parameters scope primary),
    ∀ (values : TypeBFLZJordanSourceBinding.JordanValues source),
    ∀ (jordan : TypeBFLZJordanSourceBinding.JordanCertificate source choice values),
    ∀ (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate),
    ∀ (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
      (F := F) (K := K) (p := p) (n := n)),
    letI actualFullPairAction :
        MulAction (CSp F n)
          (FullCharacterPair F K p n (source.toLiteralSource zero descent choice.dualRoots).unipotent) :=
      TypeBFLZCentralizerConjugacy.fullPairAction
        (source.toLiteralSource zero descent choice.dualRoots).unipotent
        (source.toLiteralSource zero descent choice.dualRoots).stable
    ∀ (blocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1)),
    ∀ (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
      Msys iota hinj blocks (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)),
    ∀ (union : TypeBSpecialCliffordBroueMichelSource.BlockUnionCertificate
      Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary),
    ∀ (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
      Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary hcompat),
    ∀ (productFormula : BrauerLinearTensorProductFormula iota)
        [finiteSelected : Finite (jordan.toEquation34 zero descent).rationalSeriesSource.Basic]
        (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
          (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
            (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)
        (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))
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
              (field_spinSubgroup_map n F fs) D eq35 liftTrivial c)⁻¹ * l.1.1),
    ∀ (blockSource : CharacterWeight.LocalBlockInductionSource
      (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
      (Block := LiteralPrimitiveBlock k (SpecialClifford n F))),
    ∀ (expansion : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)],
      TypeBLocalPhysicalBlockBinding.ScopedDecompositionExpansionSource (H := H) Msys),
    ∀ (upperNormalizerOrdinary : ∀ Q : Subgroup (SpecialClifford n F),
      TypeBLocalPhysicalBlockBinding.NormalizerOrdinarySource Msys blockSource.operations Q),
    ∀ (upperInflation : TypeBLocalPhysicalBlockBinding.OrdinaryInflationMembership
      Msys blockSource.operations upperNormalizerOrdinary),
    let localPhysical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
      Msys blockSource.operations iota (TypeBFLZModularRootBinding.cliffordRoot_residue Msys choice)
      expansion upperNormalizerOrdinary upperInflation
    ∀ (ambientPhysical : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
      blockSource.operations.ambientBlockData.blockIdempotent b = b.val),
    ∀ (published : PublishedOrdinaryWeightMap
          (parameters := parameters)
          (N := N)
          (fs := fs)
          (D := D)
          (radicalKernel := radicalKernel)
          (Msys := Msys)
          (scope := scope)
          (choice := choice)
          (iota := iota)
          (hinj := hinj)
          (primary := primary)
          (source := source)
          (values := values)
          (jordan := jordan)
          (zero := zero)
          (descent := descent)
          (blocks := blocks)
          (ordinary := ordinary)
          (hseries := hseries)
          (blockSource := blockSource)
      rfl localPhysical ambientPhysical),
    letI upperBlockAction :
        MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
      TypeBPhysicalBlockAction.blockAction (k := k)
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    ∀ (conlon : ∀ orbit : BlockOrbit
      (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
      (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer
          (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
          (orbitRepresentative orbit))),
    ∀ (burnside : ∀ orbit : BlockOrbit
      (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
      (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer
          (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
          (orbitRepresentative orbit))),
    ∀ (centre : TypeBCliffordCentreSource.CentreSource n F parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank)),
    ∀ (spinCompat : StableReductionBrauerCharacterCompatibility Msys iotaG),
    ∀ (separation : TypeBSpinJordanRestrictionSource.SeparationCertificate N jordan),
    let spinFamily := TypeBSpinJordanRestrictionSource.fullFamily N jordan separation
    ∀ [finiteSpinSelected : Finite
      (TypeBSpinBroueMichelCarriers.selectedFamily (ell := ell) spinFamily).Basic],
    ∀ (spinBlocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.1)),
    ∀ (spinOrdinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
      Msys iotaG hinjG spinBlocks),
    ∀ (spinUnion : TypeBSpinBroueMichelSourceBinding.BlockUnionCertificate
      spinFamily parameters.prime scope.modular_prime scope.nondefining
        Msys iotaG hinjG spinBlocks spinOrdinary),
    ∀ (spinExistsAbove : ∀ phi : IBr iotaG, ∃ chi : Irr K (Spin n F N),
      TypeBOrdinaryBlockSplitting.decompositionNumber Msys iotaG chi phi ≠ 0),
    ∀ (spinCertificate : TypeBSpinBroueMichelSourceBinding.LiteralTheorem23Certificate
      spinFamily parameters.prime scope.modular_prime scope.nondefining
        Msys iotaG hinjG spinCompat),
    ∀ (fieldNatural : ∀ (e : FieldGroup f) (s : SemisimpleParameter F p n)
      (Phi : Irr K (SpecialClifford n F)), jordan.rationalSeries s Phi →
        jordan.rationalSeries (TypeBConformalRationalProjection.semisimpleField parameters e s)
          (OrdinaryIrreducibleCharacter.twist K (SpecialClifford n F) Phi (fs.action e⁻¹))),
    ∀ (ordinary310 : TypeBSpinOrdinarySeparationBinding.Theorem310Source
      parameters scope N fs (K := K)),
    let diagonal := TypeBSpinDiagonalNormSource.diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
    letI lowerBlockAction :
        MulAction (TypeBSpinStabilizer.OuterGroup f) (LiteralPrimitiveBlock k (Spin n F N)) :=
      TypeBSpinEffectiveSourceBinding.blockAction (k := k) N diagonal fs
    ∀ (spinConlon : ∀ orbit : BlockOrbit (TypeBSpinStabilizer.OuterGroup f)
      (LiteralPrimitiveBlock k (Spin n F N)),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) (orbitRepresentative orbit))),
    ∀ (spinBurnside : ∀ orbit : BlockOrbit (TypeBSpinStabilizer.OuterGroup f)
      (LiteralPrimitiveBlock k (Spin n F N)),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) (orbitRepresentative orbit))),
    ∀ (restriction : TypeBSpinRestrictionConstituent.RestrictionExpansionSource N iota),
    ∀ (raw75 : TypeBSpinRawWeightSeparationBinding.Theorem75Source
      parameters scope N fs (K := K)),
    ∀ (spinBlockSource : CharacterWeight.LocalBlockInductionSource
      (p := ell) (k := k) (K := K) (G := Spin n F N)
      (Block := LiteralPrimitiveBlock k (Spin n F N))),
    ∀ (spinAmbientPhysical : ∀ b : LiteralPrimitiveBlock k (Spin n F N),
      spinBlockSource.operations.ambientBlockData.blockIdempotent b = b.val),
    ∀ (spinNormalizerOrdinary : ∀ Q : Subgroup (Spin n F N),
      TypeBLocalPhysicalBlockBinding.NormalizerOrdinarySource Msys spinBlockSource.operations Q),
    ∀ (spinInflation : TypeBLocalPhysicalBlockBinding.OrdinaryInflationMembership
      Msys spinBlockSource.operations spinNormalizerOrdinary),
    let spinPhysical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
      Msys spinBlockSource.operations iotaG (TypeBFLZModularRootBinding.spinRoot_residue Msys choice N)
      expansion spinNormalizerOrdinary spinInflation
    ∀ (navarro : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)]
      (rootH : PrimeRegularRootEmbedding ell k K H)
      (compatible : TypeBLocalReductionInstantiation.RootResidueCompatible Msys rootH),
      TypeBLocalReductionInstantiation.ScopedDefectZeroReductionSource Msys rootH compatible),
    let blocksBoth := blockData N blocks blockSource ambientPhysical
      spinBlocks spinBlockSource spinAmbientPhysical
    let localData := TypeBLocalReductionInstantiation.localReductionData_modular_instantiated
      N Msys choice navarro blocksBoth spinPhysical
    ∀ (coefficient : SpathCoefficientField ell k scope.modular_prime),
    ∀ (coverSource : TypeBSpinCoverSource.GenericSpinCoverSource
      (p := p) (f := f) (ell := ell) N),
    ∀ (dividesSimpleOrder : ell ∣ Nat.card (TypeBSpinCoverSource.Omega N)),
    ∀ (automorphismFacts : TypeBSpinStructuralCoverBinding.NaturalAutomorphismFacts
      N fs coverSource.rank),
    ∀ (hall : TypeBInertiaHallSource.HallPrimeToQuotientSource N ell),
    ∀ (ambientZeta : K),
    ∀ (ambientPrimitive : IsPrimitiveRoot ambientZeta
      (ell ^ (Nat.card (TypeBCriterionHypotheses.Ambient fs.action)).factorization ell)),
    letI ambientOrdinaryRoots :
        HasEnoughRootsOfUnity K (Nat.card (TypeBCriterionHypotheses.Ambient fs.action)) :=
      TypeBActualAmbientRootBinding.ambientRoots_of_primePart N fs Msys ambientZeta ambientPrimitive
    ∀ (brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k),
    ∀ (ordinaryExtension : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)],
      TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K H),
    ∀ (criterion : TypeBFullCriterionSplittingSource.Theorem45SplittingCertificate),
    let cover := TypeBSpinCoverSource.genericSpinEllPrimeCover N scope.modular_prime scope.modular_odd coverSource
    Nonempty (TypeBFullCriterionSplittingSource.NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := TypeBFixedRootCriterionFamilySplitting.downstairsFamily
        (SpinSubgroup n F N) iotaG blocksBoth scope.modular_prime hinjG localData)
      Msys cover) := by
  dsimp only
  letI ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) :=
    choice.ordinaryRoots
  letI spinOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBSpinJordanRestrictionSource.spinRoots N choice
  let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
  let iotaG := TypeBFLZModularRootBinding.spinRoot Msys choice N
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let hinjG := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG
  let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let liftTrivial := TypeBModularLinearCharacterLift.liftTrivial iota
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let radicalKernel := TypeBProposition44BroueMichelInstantiation.canonicalRadicalKernel parameters N fs iota
  intro finiteTensor
  intro finiteActing
  intro finiteUpperBlocks
  intro finiteLowerBlocks
  intro hcompat
  intro primary
  intro source
  intro values
  intro jordan
  intro zero
  intro descent
  letI actualFullPairAction :
      MulAction (CSp F n)
        (FullCharacterPair F K p n (source.toLiteralSource zero descent choice.dualRoots).unipotent) :=
    TypeBFLZCentralizerConjugacy.fullPairAction
      (source.toLiteralSource zero descent choice.dualRoots).unipotent
      (source.toLiteralSource zero descent choice.dualRoots).stable
  intro blocks
  intro ordinary
  intro union
  intro literal23
  intro productFormula finiteSelected hseries eq35 tensorLabel tensor_character tensor_parameter
  intro blockSource
  intro expansion
  intro upperNormalizerOrdinary
  intro upperInflation
  let localPhysical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
    Msys blockSource.operations iota (TypeBFLZModularRootBinding.cliffordRoot_residue Msys choice)
    expansion upperNormalizerOrdinary upperInflation
  intro ambientPhysical
  intro published
  letI upperBlockAction :
      MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
    TypeBPhysicalBlockAction.blockAction (k := k)
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  intro conlon
  intro burnside
  intro centre
  intro spinCompat
  intro separation
  let spinFamily := TypeBSpinJordanRestrictionSource.fullFamily N jordan separation
  intro finiteSpinSelected
  intro spinBlocks
  intro spinOrdinary
  intro spinUnion
  intro spinExistsAbove
  intro spinCertificate
  intro fieldNatural
  intro ordinary310
  let diagonal := TypeBSpinDiagonalNormSource.diagonalSource n F N parameters
    (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
  letI lowerBlockAction :
      MulAction (TypeBSpinStabilizer.OuterGroup f) (LiteralPrimitiveBlock k (Spin n F N)) :=
    TypeBSpinEffectiveSourceBinding.blockAction (k := k) N diagonal fs
  intro spinConlon
  intro spinBurnside
  intro restriction
  intro raw75
  intro spinBlockSource
  intro spinAmbientPhysical
  intro spinNormalizerOrdinary
  intro spinInflation
  let spinPhysical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
    Msys spinBlockSource.operations iotaG (TypeBFLZModularRootBinding.spinRoot_residue Msys choice N)
    expansion spinNormalizerOrdinary spinInflation
  intro navarro
  let blocksBoth := blockData N blocks blockSource ambientPhysical
    spinBlocks spinBlockSource spinAmbientPhysical
  let localData := TypeBLocalReductionInstantiation.localReductionData_modular_instantiated
    N Msys choice navarro blocksBoth spinPhysical
  intro coefficient
  intro coverSource
  intro dividesSimpleOrder
  intro automorphismFacts
  intro hall
  intro ambientZeta
  intro ambientPrimitive
  letI ambientOrdinaryRoots :
      HasEnoughRootsOfUnity K (Nat.card (TypeBCriterionHypotheses.Ambient fs.action)) :=
    TypeBActualAmbientRootBinding.ambientRoots_of_primePart N fs Msys ambientZeta ambientPrimitive
  intro brauerExtension
  intro ordinaryExtension
  intro criterion
  let cover := TypeBSpinCoverSource.genericSpinEllPrimeCover N scope.modular_prime scope.modular_odd coverSource
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D
    (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) iota productFormula
  letI := tensorFieldSemidirectAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D radicalKernel
  obtain ⟨omega, equivariant, block⟩ :=
    TypeBProposition44BroueMichelInstantiation.specialClifford_proposition_4_4_broue_michel_instantiated
      (parameters := parameters) (N := N) (fs := fs) (Msys := Msys)
      (scope := scope) (choice := choice)
      hcompat primary source values jordan zero descent blocks ordinary union literal23
      productFormula hseries eq35 tensorLabel tensor_character tensor_parameter
      blockSource localPhysical ambientPhysical published conlon burnside
  have constituent : ConstituentClause (SpinSubgroup n F N) fs.action (naturalAction N fs)
      iota iotaG := by
    intro Phi
    obtain ⟨phi, occurs, factorization⟩ :=
      TypeBSpinConstituentInstantiation.exists_spin_constituent_with_ambient_factorization_modular_instantiated
        jordan fs centre Msys spinCompat separation spinBlocks spinOrdinary spinUnion
        spinExistsAbove spinCertificate fieldNatural ordinary310 spinConlon spinBurnside restriction Phi
    refine ⟨phi, occurs, ?_⟩
    simpa only [BrauerFactorization, factorInertia, embeddedM, embeddedE, brauerInertia,
      naturalAction, TypeBSpinAmbientFactorizationBinding.ambientBrauerInertia,
      TypeBSpinAmbientFactorizationBinding.specialCliffordInertiaImage,
      TypeBSpinAmbientFactorizationBinding.fieldInertiaImage,
      Subgroup.map_comap_eq, inf_comm] using factorization
  let hypotheses : AllBlocksHypotheses (SpinSubgroup n F N) fs.action (naturalAction N fs)
      iota iotaG blocksBoth hinj (field_spinSubgroup_map n F fs) D productFormula radicalKernel :=
    { prime := scope.modular_prime
      coefficient := coefficient
      cover := cover
      divides_simple_order := dividesSimpleOrder
      structural := TypeBSpinStructuralCoverBinding.structural N fs coverSource automorphismFacts
      rootAgreement := TypeBFLZModularRootBinding.spinRoot_agrees Msys choice N
      brauer_injective_downstairs := hinjG
      localReduction := localData
      liftCompatible := liftCompatible
      lift_primeTo := fun c =>
        (TypeBModularLinearCharacterLift.liftCharacter_order_coprime iota c.val).symm
      lift_trivial := liftTrivial
      extensions := TypeBSpinExtensionInstantiation.extensionClauses_modular_instantiated
        N fs Msys choice brauerExtension ordinaryExtension
      correspondence := { omega := omega, equivariant := equivariant, block := block }
      hall := hallData N hall
      JG := TypeBSpinHallJGInstantiation.allPairsJG_modular_instantiated
        parameters scope N fs centre Msys choice hall
      constituent := constituent
      rawNormalizer := TypeBSpinRawWeightSeparationBinding.rawNormalizerClause
        parameters scope N fs raw75 }
  exact ⟨TypeBFullCriterionSplittingSource.witness Msys
    (SpinSubgroup n F N) fs.action (naturalAction N fs) iota iotaG
    (TypeBModularGroupRootBinding.cliffordRoot_eq_groupRoot Msys choice)
    (TypeBModularGroupRootBinding.spinRoot_eq_groupRoot Msys choice N)
    blocksBoth localPhysical hinj (field_spinSubgroup_map n F fs) D productFormula radicalKernel
    hypotheses criterion⟩

end ModularRep.PaperProofs.TypeBProposition44FullInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
