import ManuscriptIBAW.TypeB.OddConlon
import ModularRep.PaperProofs.TypeBProposition44GenericInputs

/-!
# The Type B application at odd primes

The published assumptions concern the same specified groups, characters and
actions. Lemma 4.2 supplies the block bijections through the central
character argument. The construction from ordinary characters to weights and
transfer of ordinary stabilisers to Brauer characters then give every
hypothesis of the complete criterion.

The family and cover are fixed before applying the criterion. Published
character theory, the interpretations of rational series and blocks, and the
complete criterion remain explicit source assumptions.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ManuscriptIBAW.TypeB.OddApplication

open ModularRep ModularRep.PaperProofs
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero IntegralBasicSetBridge OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesSplitting
open TypeBFLZLabelSource (FullCharacterPair SemisimpleParameter CharacterPair Applicability)
open TypeBFLZLabelSplittingSource TypeBConlonBlockRelative
open OddConformalProposition311Relative TypeBOddPrimesProposition44Relative
open TypeBConlonBlockSourceInstantiation ConlonBasicSet
open TypeBConlonPhysicalActionInstantiation TypeBSpecialCliffordActionSplitting
open OddConlonOrbitAssembly TypeCWeightTensorFieldAction
open TypeBProposition44OrdinaryWeightBinding
open TypeBCriterionHypotheses TypeBCriterionCarrierBindings
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)
variable (Msys : ModularSystem ell K O k) (scope : Applicability p ell n)
variable (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)

local instance oddApplicationCliffordFintype : Fintype (SpecialClifford n F) := Fintype.ofFinite _
local instance oddApplicationSpinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

attribute [local instance] TypeBFLZJordanSourceBinding.actualFullPairAction

local notation "iota" => TypeBFLZModularRootBinding.cliffordRoot Msys choice
local notation "iotaG" => TypeBFLZModularRootBinding.spinRoot Msys choice N
local notation "hinj" => irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
local notation "hinjG" => irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG
local notation "D" => TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
local notation "liftTrivial" => TypeBModularLinearCharacterLift.liftTrivial iota
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
local notation "radicalKernel" =>
  TypeBProposition44BroueMichelInstantiation.canonicalRadicalKernel parameters N fs iota

local instance oddApplicationUpperBlockAction :
    MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
  TypeBPhysicalBlockAction.blockAction (k := k)
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)

section Data

variable [upperRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
variable [lowerRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- The independent data for the specified generic cover. The structure below
obtains both ordinary splitting instances from its ordinary choice. -/
structure Data
    (coverSource : TypeBSpinCoverSource.GenericSpinCoverSource
      (p := p) (f := f) (ell := ell) N)
    (divides : ell ∣ Nat.card (TypeBSpinCoverSource.Omega N)) where
  [finiteTensor : Finite (TensorCharacters (k := k) (SpinSubgroup n F N))]
  [finiteActing : Finite (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs))]
  [finiteUpperBlocks : Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
  [finiteLowerBlocks : Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  hcompat : StableReductionBrauerCharacterCompatibility Msys iota
  primary : TypeBFLZPrimarySource.PrimarySource parameters scope
  source : TypeBFLZOccurringCharacterSource.OccurringCharacterSource
    (K := K) parameters scope primary
  values : TypeBFLZJordanSourceBinding.JordanValues source
  jordan : TypeBFLZJordanSourceBinding.JordanCertificate source choice values
  zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate
  descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
    (F := F) (K := K) (p := p) (n := n)
  blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1)
  ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks
    (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)
  union : TypeBSpecialCliffordBroueMichelSource.BlockUnionCertificate
    Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary
  literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
    Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary hcompat
  productFormula : BrauerLinearTensorProductFormula iota
  [finiteSelected : Finite (jordan.toEquation34 zero descent).rationalSeriesSource.Basic]
  hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
    (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
  blockSource : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
    (Block := LiteralPrimitiveBlock k (SpecialClifford n F))
  expansion : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)],
    TypeBLocalPhysicalBlockBinding.ScopedDecompositionExpansionSource (H := H) Msys
  upperNormalizerOrdinary : ∀ Q : Subgroup (SpecialClifford n F),
    TypeBLocalPhysicalBlockBinding.NormalizerOrdinarySource Msys blockSource.operations Q
  upperInflation : TypeBLocalPhysicalBlockBinding.OrdinaryInflationMembership
    Msys blockSource.operations upperNormalizerOrdinary
  ambientPhysical : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
    blockSource.operations.ambientBlockData.blockIdempotent b = b.val
  published : PublishedOrdinaryWeightMap
    (parameters := parameters) (N := N) (fs := fs) («D» := D)
    («radicalKernel» := radicalKernel) (Msys := Msys) (scope := scope) (choice := choice)
    («iota» := iota) («hinj» := hinj) (primary := primary) (source := source) (values := values)
    (jordan := jordan) (zero := zero) (descent := descent) (blocks := blocks)
    (ordinary := ordinary) (hseries := hseries) (blockSource := blockSource)
    rfl
    (TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility Msys blockSource.operations iota
      (TypeBFLZModularRootBinding.cliffordRoot_residue Msys choice)
      expansion upperNormalizerOrdinary upperInflation)
    ambientPhysical
  conlon : ∀ orbit : BlockOrbit
    (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
    (LiteralPrimitiveBlock k (SpecialClifford n F)),
    PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer
        (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
        (orbitRepresentative orbit))
  burnside : ∀ orbit : BlockOrbit
    (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
    (LiteralPrimitiveBlock k (SpecialClifford n F)),
    PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer
        (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
        (orbitRepresentative orbit))
  centre : TypeBCliffordCentreSource.CentreSource n F parameters
    (Nat.le_trans (by decide : 1 ≤ 3) scope.rank)
  spinCompat : StableReductionBrauerCharacterCompatibility Msys iotaG
  separation : TypeBSpinJordanRestrictionSource.SeparationCertificate N jordan
  [finiteSpinSelected : Finite (TypeBSpinBroueMichelCarriers.selectedFamily (ell := ell)
    (TypeBSpinJordanRestrictionSource.fullFamily N jordan separation)).Basic]
  spinBlocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.1)
  spinOrdinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iotaG hinjG spinBlocks
  spinUnion : TypeBSpinBroueMichelSourceBinding.BlockUnionCertificate
    (TypeBSpinJordanRestrictionSource.fullFamily N jordan separation)
    parameters.prime scope.modular_prime scope.nondefining Msys iotaG hinjG spinBlocks spinOrdinary
  spinExistsAbove : ∀ phi : IBr iotaG, ∃ chi : Irr K (Spin n F N),
    TypeBOrdinaryBlockSplitting.decompositionNumber Msys iotaG chi phi ≠ 0
  spinCertificate : TypeBSpinBroueMichelSourceBinding.LiteralTheorem23Certificate
    (TypeBSpinJordanRestrictionSource.fullFamily N jordan separation)
    parameters.prime scope.modular_prime scope.nondefining Msys iotaG hinjG spinCompat
  fieldNatural : ∀ (e : FieldGroup f) (s : SemisimpleParameter F p n)
    (Phi : Irr K (SpecialClifford n F)), jordan.rationalSeries s Phi →
    jordan.rationalSeries (TypeBConformalRationalProjection.semisimpleField parameters e s)
      (OrdinaryIrreducibleCharacter.twist K (SpecialClifford n F) Phi (fs.action e⁻¹))
  ordinary310 : TypeBSpinOrdinarySeparationBinding.Theorem310Source parameters scope N fs (K := K)
  spinConlon :
    let diagonal := TypeBSpinDiagonalNormSource.diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
    letI : MulAction (TypeBSpinStabilizer.OuterGroup f) (LiteralPrimitiveBlock k (Spin n F N)) :=
      TypeBSpinEffectiveSourceBinding.blockAction (k := k) N diagonal fs
    ∀ orbit : BlockOrbit (TypeBSpinStabilizer.OuterGroup f)
      (LiteralPrimitiveBlock k (Spin n F N)),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) (orbitRepresentative orbit))
  spinBurnside :
    let diagonal := TypeBSpinDiagonalNormSource.diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
    letI : MulAction (TypeBSpinStabilizer.OuterGroup f) (LiteralPrimitiveBlock k (Spin n F N)) :=
      TypeBSpinEffectiveSourceBinding.blockAction (k := k) N diagonal fs
    ∀ orbit : BlockOrbit (TypeBSpinStabilizer.OuterGroup f)
      (LiteralPrimitiveBlock k (Spin n F N)),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) (orbitRepresentative orbit))
  restriction : TypeBSpinRestrictionConstituent.RestrictionExpansionSource N iota
  raw75 : TypeBSpinRawWeightSeparationBinding.Theorem75Source parameters scope N fs (K := K)
  spinBlockSource : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := Spin n F N)
    (Block := LiteralPrimitiveBlock k (Spin n F N))
  spinAmbientPhysical : ∀ b : LiteralPrimitiveBlock k (Spin n F N),
    spinBlockSource.operations.ambientBlockData.blockIdempotent b = b.val
  spinNormalizerOrdinary : ∀ Q : Subgroup (Spin n F N),
    TypeBLocalPhysicalBlockBinding.NormalizerOrdinarySource Msys spinBlockSource.operations Q
  spinInflation : TypeBLocalPhysicalBlockBinding.OrdinaryInflationMembership
    Msys spinBlockSource.operations spinNormalizerOrdinary
  navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (rootH : PrimeRegularRootEmbedding ell k K H)
    (compatible : TypeBLocalReductionInstantiation.RootResidueCompatible Msys rootH),
    TypeBLocalReductionInstantiation.ScopedDefectZeroReductionSource Msys rootH compatible
  coefficient : SpathCoefficientField ell k scope.modular_prime
  automorphismFacts : TypeBSpinStructuralCoverBinding.NaturalAutomorphismFacts N fs coverSource.rank
  hall : TypeBInertiaHallSource.HallPrimeToQuotientSource N ell
  ambientZeta : K
  ambientPrimitive : IsPrimitiveRoot ambientZeta
    (ell ^ (Nat.card (TypeBCriterionHypotheses.Ambient fs.action)).factorization ell)
  brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k
  ordinaryExtension : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)],
    TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K H
  criterion : TypeBFullCriterionSplittingSource.Theorem45SplittingCertificate

end Data

/-- The inputs, with both splitting instances obtained from the same ordinary
choice. -/
abbrev Inputs
    (coverSource : TypeBSpinCoverSource.GenericSpinCoverSource
      (p := p) (f := f) (ell := ell) N)
    (divides : ell ∣ Nat.card (TypeBSpinCoverSource.Omega N)) : Type := by
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := choice.ordinaryRoots
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBSpinJordanRestrictionSource.spinRoots N choice
  exact Data parameters N fs Msys scope choice coverSource divides

variable (coverSource : TypeBSpinCoverSource.GenericSpinCoverSource
  (p := p) (f := f) (ell := ell) N)
variable (divides : ell ∣ Nat.card (TypeBSpinCoverSource.Omega N))
variable (inputs : Inputs parameters N fs Msys scope choice coverSource divides)

/-- The specified family on Spin. -/
def family : Definition35Family ell := by
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := choice.ordinaryRoots
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBSpinJordanRestrictionSource.spinRoots N choice
  letI := inputs.finiteUpperBlocks
  letI := inputs.finiteLowerBlocks
  let blocksBoth := TypeBProposition44FullInstantiation.blockData N
    inputs.blocks inputs.blockSource inputs.ambientPhysical
    inputs.spinBlocks inputs.spinBlockSource inputs.spinAmbientPhysical
  let physical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
    Msys inputs.spinBlockSource.operations iotaG
    (TypeBFLZModularRootBinding.spinRoot_residue Msys choice N)
    inputs.expansion inputs.spinNormalizerOrdinary inputs.spinInflation
  let localData := TypeBLocalReductionInstantiation.localReductionData_modular_instantiated
    N Msys choice inputs.navarro blocksBoth physical
  exact TypeBFixedRootCriterionFamilySplitting.downstairsFamily
    (SpinSubgroup n F N) iotaG blocksBoth scope.modular_prime hinjG localData

@[simp]
theorem family_H :
    (family parameters N fs Msys scope choice coverSource divides inputs).H = Spin n F N := rfl

@[simp]
theorem family_K :
    (family parameters N fs Msys scope choice coverSource divides inputs).K = K := rfl

@[simp]
theorem family_k :
    (family parameters N fs Msys scope choice coverSource divides inputs).k = k := rfl

/-- The cover is fixed before the application and has the specified quotient. -/
def cover : EllPrimeCoverSource ell (family parameters N fs Msys scope choice coverSource divides inputs).H :=
  TypeBSpinCoverSource.genericSpinEllPrimeCover N scope.modular_prime scope.modular_odd coverSource

@[simp]
theorem cover_S :
    (cover parameters N fs Msys scope choice coverSource divides inputs).S =
      TypeBSpinCoverSource.Omega N := rfl

@[simp]
theorem cover_quotient :
    (cover parameters N fs Msys scope choice coverSource divides inputs).quotient =
      QuotientGroup.mk' (Subgroup.center (Spin n F N)) := rfl

/-- The correspondence for the special Clifford group. Conlon's theorem is
applied on each block orbit, followed by the separate published map from the
same ordinary characters to weights. -/
def correspondence := by
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := choice.ordinaryRoots
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBSpinJordanRestrictionSource.spinRoots N choice
  letI := inputs.finiteTensor
  letI := inputs.finiteActing
  letI := inputs.finiteUpperBlocks
  letI := inputs.finiteLowerBlocks
  letI := inputs.finiteSelected
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D
    (inputs.jordan.toEquation34 inputs.zero inputs.descent).rationalSeriesSource.selectedSeries inputs.hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) iota inputs.productFormula
  letI := tensorFieldSemidirectAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D radicalKernel
  let blocksBoth := TypeBProposition44FullInstantiation.blockData N
    inputs.blocks inputs.blockSource inputs.ambientPhysical
    inputs.spinBlocks inputs.spinBlockSource inputs.spinAmbientPhysical
  have derived :=
    TypeBProposition44OrdinaryWeightBinding.assemble_of_derived_lemma43
      (parameters := parameters) (N := N) (fs := fs) («D» := D)
      («radicalKernel» := radicalKernel) (Msys := Msys) (scope := scope) (choice := choice)
      («iota» := iota) («hinj» := hinj) (primary := inputs.primary) (source := inputs.source)
      (values := inputs.values) (jordan := inputs.jordan) (zero := inputs.zero) (descent := inputs.descent)
      (blocks := inputs.blocks) (ordinary := inputs.ordinary) (hseries := inputs.hseries)
      (blockSource := inputs.blockSource) (canonicalLift := rfl)
      (localPhysical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
        Msys inputs.blockSource.operations iota
        (TypeBFLZModularRootBinding.cliffordRoot_residue Msys choice)
        inputs.expansion inputs.upperNormalizerOrdinary inputs.upperInflation)
      (ambientPhysical := inputs.ambientPhysical)
      (published := inputs.published) inputs.hcompat inputs.productFormula
      (TypeBModularLinearCharacterLift.liftCompatible iota (SpinSubgroup n F N)
        fs.action (field_spinSubgroup_map n F fs)) (by
        intro orbit
        obtain ⟨_, beta, hbeta⟩ := OddConlon.block_bijection fs D Msys iota hinj
          inputs.hcompat (inputs.jordan.toEquation34 inputs.zero inputs.descent)
          inputs.blocks inputs.ordinary inputs.union inputs.literal23
          inputs.productFormula inputs.hseries
          (TypeBModularLinearCharacterLift.liftCompatible iota (SpinSubgroup n F N)
            fs.action (field_spinSubgroup_map n F fs))
          inputs.centre (orbitRepresentative orbit) (inputs.conlon orbit) (inputs.burnside orbit)
        refine ⟨beta, ?_⟩
        intro a ha phi
        exact congrArg Subtype.val (hbeta ⟨a, ha⟩ phi))
  exact (show GlobalCorrespondence (SpinSubgroup n F N) fs.action iota blocksBoth
    hinj (field_spinSubgroup_map n F fs) D inputs.productFormula radicalKernel from
      ⟨Classical.choose derived, (Classical.choose_spec derived).1, (Classical.choose_spec derived).2⟩)

/-- Every criterion hypothesis is constructed on the original family. The
separation theorem for ordinary Spin characters is transferred through the
global bijection before choosing a constituent of a restriction. -/
def hypotheses := by
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := choice.ordinaryRoots
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBSpinJordanRestrictionSource.spinRoots N choice
  letI := inputs.finiteTensor
  letI := inputs.finiteActing
  letI := inputs.finiteUpperBlocks
  letI := inputs.finiteLowerBlocks
  letI := inputs.finiteSelected
  letI := inputs.finiteSpinSelected
  let blocksBoth := TypeBProposition44FullInstantiation.blockData N
    inputs.blocks inputs.blockSource inputs.ambientPhysical
    inputs.spinBlocks inputs.spinBlockSource inputs.spinAmbientPhysical
  let spinPhysical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
    Msys inputs.spinBlockSource.operations iotaG
    (TypeBFLZModularRootBinding.spinRoot_residue Msys choice N)
    inputs.expansion inputs.spinNormalizerOrdinary inputs.spinInflation
  let localData := TypeBLocalReductionInstantiation.localReductionData_modular_instantiated
    N Msys choice inputs.navarro blocksBoth spinPhysical
  letI : HasEnoughRootsOfUnity K (Nat.card (Ambient fs.action)) :=
    TypeBActualAmbientRootBinding.ambientRoots_of_primePart N fs Msys
      inputs.ambientZeta inputs.ambientPrimitive
  have constituent : ConstituentClause (SpinSubgroup n F N) fs.action (naturalAction N fs)
      iota iotaG := by
    intro Phi
    obtain ⟨phi, occurs, factorization⟩ :=
      TypeBSpinConstituentInstantiation.exists_spin_constituent_with_ambient_factorization_modular_instantiated
        inputs.jordan fs inputs.centre Msys inputs.spinCompat inputs.separation
        inputs.spinBlocks inputs.spinOrdinary inputs.spinUnion inputs.spinExistsAbove
        inputs.spinCertificate inputs.fieldNatural inputs.ordinary310
        inputs.spinConlon inputs.spinBurnside inputs.restriction Phi
    refine ⟨phi, occurs, ?_⟩
    simpa only [BrauerFactorization, factorInertia, embeddedM, embeddedE, brauerInertia,
      naturalAction, TypeBSpinAmbientFactorizationBinding.ambientBrauerInertia,
      TypeBSpinAmbientFactorizationBinding.specialCliffordInertiaImage,
      TypeBSpinAmbientFactorizationBinding.fieldInertiaImage,
      Subgroup.map_comap_eq, inf_comm] using factorization
  exact (show AllBlocksHypotheses (SpinSubgroup n F N) fs.action (naturalAction N fs)
      iota iotaG blocksBoth hinj (field_spinSubgroup_map n F fs) D
      inputs.productFormula radicalKernel from
    { prime := scope.modular_prime
      coefficient := inputs.coefficient
      cover := TypeBSpinCoverSource.genericSpinEllPrimeCover N
        scope.modular_prime scope.modular_odd coverSource
      divides_simple_order := divides
      structural := TypeBSpinStructuralCoverBinding.structural N fs coverSource inputs.automorphismFacts
      rootAgreement := TypeBFLZModularRootBinding.spinRoot_agrees Msys choice N
      brauer_injective_downstairs := hinjG
      localReduction := localData
      liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      lift_primeTo := fun c =>
        (TypeBModularLinearCharacterLift.liftCharacter_order_coprime iota c.val).symm
      lift_trivial := liftTrivial
      extensions := TypeBSpinExtensionInstantiation.extensionClauses_modular_instantiated
        N fs Msys choice inputs.brauerExtension inputs.ordinaryExtension
      correspondence := correspondence parameters N fs Msys scope choice coverSource divides inputs
      hall := hallData N inputs.hall
      JG := TypeBSpinHallJGInstantiation.allPairsJG_modular_instantiated
        parameters scope N fs inputs.centre Msys choice inputs.hall
      constituent := constituent
      rawNormalizer := TypeBSpinRawWeightSeparationBinding.rawNormalizerClause
        parameters scope N fs inputs.raw75 })

/-- Apply the complete published criterion to the hypotheses on the fixed family
and cover over the same modular system. -/
def witness : TypeBFullCriterionSplittingSource.NormalizedFamilyWitness
    (familyAlgebra := (show Algebra O K from inferInstance))
    (family := family parameters N fs Msys scope choice coverSource divides inputs)
    Msys (cover parameters N fs Msys scope choice coverSource divides inputs) := by
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := choice.ordinaryRoots
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBSpinJordanRestrictionSource.spinRoots N choice
  letI := inputs.finiteTensor
  letI := inputs.finiteActing
  letI := inputs.finiteUpperBlocks
  letI := inputs.finiteLowerBlocks
  letI : HasEnoughRootsOfUnity K (Nat.card (Ambient fs.action)) :=
    TypeBActualAmbientRootBinding.ambientRoots_of_primePart N fs Msys
      inputs.ambientZeta inputs.ambientPrimitive
  let blocksBoth := TypeBProposition44FullInstantiation.blockData N
    inputs.blocks inputs.blockSource inputs.ambientPhysical
    inputs.spinBlocks inputs.spinBlockSource inputs.spinAmbientPhysical
  let localPhysical := TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility
    Msys inputs.blockSource.operations iota (TypeBFLZModularRootBinding.cliffordRoot_residue Msys choice)
    inputs.expansion inputs.upperNormalizerOrdinary inputs.upperInflation
  exact TypeBFullCriterionSplittingSource.witness Msys
    (SpinSubgroup n F N) fs.action (naturalAction N fs) iota iotaG
    (TypeBModularGroupRootBinding.cliffordRoot_eq_groupRoot Msys choice)
    (TypeBModularGroupRootBinding.spinRoot_eq_groupRoot Msys choice N)
    blocksBoth localPhysical hinj (field_spinSubgroup_map n F fs) D inputs.productFormula radicalKernel
    (hypotheses parameters N fs Msys scope choice coverSource divides inputs) inputs.criterion

end ManuscriptIBAW.TypeB.OddApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/

