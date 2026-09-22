import ModularRep.PaperProofs.TypeBProposition44CoveringBlockRestriction

/-!
# Source-instantiated covering-block correspondence for Proposition 4.3

The SAME accepted ordinary-source and Conlon--Burnside consumer constructs
the global correspondence. Its restriction to each actual Spin covering
set is then K, with the full tensor and covering-set field stabilizer.
No global or blockwise Brauer correspondence is an external input here.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBProposition44CoveringInstantiation

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

open OddConlonOrbitAssembly TypeCWeightTensorFieldAction
open TypeBProposition44OrdinaryWeightBinding

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)
local instance cliffordFintype : Fintype (SpecialClifford n F) := Fintype.ofFinite _

open TypeBProposition44BroueMichelInstantiation (canonicalRadicalKernel)
open TypeBProposition44CoveringBlockRestriction

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
/-- The complete covering-union correspondence clause, with every matching derived. -/
theorem specialClifford_covering_blocks_instantiated :
    let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
    let hinj : IrreducibleBrauerCharacterInjectivity iota :=
      irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftTrivial := TypeBModularLinearCharacterLift.liftTrivial iota
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let radicalKernel := canonicalRadicalKernel parameters N fs iota
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
          (field_spinSubgroup_map n F fs) D eq35 liftTrivial c)⁻¹ * l.1.1)
    (blockSource : CharacterWeight.LocalBlockInductionSource
      (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
      (Block := LiteralPrimitiveBlock k (SpecialClifford n F)))
    (localPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
      iota blockSource.operations)
    (ambientPhysical : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
      blockSource.operations.ambientBlockData.blockIdempotent b = b.val)
    (published : PublishedOrdinaryWeightMap
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
    letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) :=
      (jordan.toEquation34 zero descent).ordinary_roots
    letI := TypeBPhysicalBlockAction.blockAction (k := k)
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D
      (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries hseries
    letI := brauerCharacterAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) iota productFormula
    letI := tensorFieldSemidirectAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D radicalKernel
    ∀ (conlon : ∀ orbit : BlockOrbit (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (orbitRepresentative orbit)))
      (burnside : ∀ orbit : BlockOrbit (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (orbitRepresentative orbit))),
    ∃ (omega : IBr iota ≃ CharacterWeight.ConjugacyClass
        (p := ell) (K := K) (G := SpecialClifford n F))
      (equivariant : ∀ (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (phi : IBr iota),
        omega (a • phi) = a • omega phi)
      (block : ∀ phi : IBr iota, blockSource.weightBlock (omega phi) =
        irreducibleBrauerCharacterBlock iota hinj blocks phi),
    ∀ b : LiteralPrimitiveBlock k (Spin n F N),
      letI := brauerCoveringAction N fs iota hinj blocks productFormula b
      letI := weightCoveringAction N fs iota hinj blocks productFormula D radicalKernel
        blockSource omega block equivariant b
      ∃ e : brauerCoveringDomain N iota hinj blocks b ≃ weightCoveringDomain N blockSource b,
        (∀ phi, (e phi).val = omega phi.val) ∧
        (∀ (a : coveringStabilizer N fs b) phi, e (a • phi) = a • e phi) ∧
        (∀ phi, blockSource.weightBlock (e phi).val =
          irreducibleBrauerCharacterBlock iota hinj blocks phi.val) := by
  dsimp only
  intro hcompat primary source values jordan zero descent blocks ordinary union literal23
    productFormula finiteBasic hseries eq35 tensorLabel tensor_character tensor_parameter
    blockSource localPhysical ambientPhysical published conlon burnside
  let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
  let hinj : IrreducibleBrauerCharacterInjectivity iota :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let radicalKernel := canonicalRadicalKernel parameters N fs iota
  obtain ⟨omega, equivariant, block⟩ :=
    TypeBProposition44BroueMichelInstantiation.specialClifford_proposition_4_4_broue_michel_instantiated
      (parameters := parameters) (N := N) (fs := fs) (Msys := Msys)
      (scope := scope) (choice := choice)
      hcompat primary source values jordan zero descent blocks ordinary union literal23
      productFormula hseries eq35 tensorLabel tensor_character tensor_parameter
      blockSource localPhysical ambientPhysical published conlon burnside
  refine ⟨omega, equivariant, block, ?_⟩
  intro b
  refine ⟨restrict N iota hinj blocks blockSource omega block b, ?_, ?_, ?_⟩
  · intro phi
    rfl
  · exact restrict_equivariant N fs iota hinj blocks productFormula D radicalKernel
      blockSource omega block equivariant b
  · intro phi
    exact block phi.val

end ModularRep.PaperProofs.TypeBProposition44CoveringInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
