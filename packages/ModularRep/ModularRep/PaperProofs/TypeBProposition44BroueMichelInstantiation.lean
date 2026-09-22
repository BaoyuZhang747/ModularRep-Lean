import ModularRep.PaperProofs.TypeBConlonBroueMichelInstantiation
import ModularRep.PaperProofs.TypeBProposition44OrdinaryWeightBinding

/-!
# The concrete same-source Proposition 4.3 correspondence

The accepted Broue--Michel Lemma 4.2 deduction supplies the representative
Brauer-to-ordinary equivalences. The published ordinary-to-weight map is
the separate FLZ Proposition 7.2 source on the same Jordan family, actual
local quotient characters and specified block allocations. Construction from orbit representatives
is reused without a blockwise or representative correspondence source.

The canonical full ell-prime quotient-character lift and its radical-kernel
property are constructed on the same modular root. This file asserts the
global equivariant block-preserving bijection, not the full criterion or
iBAW conclusion. Source realization limits remain those of the two exact
source providers. No ordinary algebraic closure or resource override occurs.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBProposition44BroueMichelInstantiation

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

/-- The canonical ordinary lift has ell-prime order, hence kills every
actual radical ell-subgroup. No radical-kernel or order source is supplied. -/
def canonicalRadicalKernel
    (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F)) :
    RadicalKernelLiftInput (p := ell)
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      (TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) := by
  apply TypeBRadicalLiftKernel.radicalKernelLiftInput_of_primeToOrder
  intro c
  change ell.Coprime (orderOf (TypeBModularLinearCharacterLift.liftCharacter iota c.val))
  exact (TypeBModularLinearCharacterLift.liftCharacter_order_coprime iota c.val).symm

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

variable
    (productFormula : BrauerLinearTensorProductFormula iota)
    [finiteSelected : Finite (jordan.toEquation34 zero descent).rationalSeriesSource.Basic]
    (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)
    (liftCompatible : OrdinaryLiftReductionCompatible (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D iota)
    (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))
    (liftTrivial : ∀ c : TensorCharacters (k := k) (SpinSubgroup n F N),
      TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
        (G0 := (SpinSubgroup n F N)) (field := fs.action) (hinvariant := (field_spinSubgroup_map n F fs)) D c ∈
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


variable (radicalKernel : RadicalKernelLiftInput (p := ell)
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D)
variable (canonicalLift : D =
  TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable (blockSource : CharacterWeight.LocalBlockInductionSource
  (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
  (Block := LiteralPrimitiveBlock k (SpecialClifford n F)))
variable (localPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
  iota blockSource.operations)
variable (ambientPhysical : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
  blockSource.operations.ambientBlockData.blockIdempotent b = b.val)
variable (published : PublishedOrdinaryWeightMap
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
  canonicalLift localPhysical ambientPhysical)


include hcompat union literal23 liftCompatible eq35 liftTrivial tensor_character tensor_parameter
  finiteSelected published in
/-- Every representative bijection is derived from the accepted full Lemma 4.2
on the same specified blocks, then composed with the exact published ordinary
weight map. No representative or blockwise matching is a hypothesis. -/
theorem specialClifford_proposition_4_4_broue_michel_relative :
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
    ∃ omega : IBr iota ≃ CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F),
      (∀ (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (phi : IBr iota),
        omega (a • phi) = a • omega phi) ∧
      (∀ phi : IBr iota, blockSource.weightBlock (omega phi) =
        irreducibleBrauerCharacterBlock iota hinj blocks phi) := by
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
  intro conlon burnside
  let ordinaryBlock := ordinarySeriesBlockMap
    (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
    (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock
  let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
  have hBrBlock := TypeBPhysicalBlockAction.brauerBlockEquivariant
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    iota productFormula hinj blocks
  have representativeMaps : RepresentativeEquivExists
      brauerBlock ordinaryBlock hBrBlock := by
    intro orbit
    let b := orbitRepresentative orbit
    have hlocal :=
      TypeBConlonBroueMichelInstantiation.specialClifford_lemma_4_3_broue_michel_relative
        (parameters := parameters)
        (N := N)
        (fs := fs)
        (D := D)
        (Msys := Msys)
        (iota := iota)
        (hinj := hinj)
        (hcompat := hcompat)
        (scope := scope)
        (choice := choice)
        (primary := primary)
        (source := source)
        (values := values)
        (jordan := jordan)
        (zero := zero)
        (descent := descent)
        (blocks := blocks)
        (ordinary := ordinary)
        (union := union)
        (literal23 := literal23)
        (productFormula := productFormula)
        (hseries := hseries)
        (liftCompatible := liftCompatible)
        (eq35 := eq35)
        (liftTrivial := liftTrivial)
        (tensorLabel := tensorLabel)
        (tensor_character := tensor_character)
        (tensor_parameter := tensor_parameter)
        (b := b) (conlon orbit) (burnside orbit)
    rcases hlocal with ⟨_, _, e, he⟩
    refine ⟨e, ?_⟩
    intro a hfix phi
    let j : MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b := ⟨a, hfix⟩
    have hj := he j phi
    exact congrArg Subtype.val hj
  exact assemble_of_derived_lemma43
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
    (canonicalLift := canonicalLift)
    (localPhysical := localPhysical)
    (ambientPhysical := ambientPhysical)
    (published := published)
    hcompat productFormula liftCompatible representativeMaps


/-- Concrete Proposition 4.3 correspondence construction. The modular root, Brauer
separation, full ell-prime ordinary lift and radical-kernel proof are fixed
before the exact published source inputs. The conclusion is only the
actual global equivariant, block-preserving character-weight equivalence. -/
theorem specialClifford_proposition_4_4_broue_michel_instantiated :
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
    ∃ omega : IBr iota ≃ CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F),
      (∀ (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (phi : IBr iota),
        omega (a • phi) = a • omega phi) ∧
      (∀ phi : IBr iota, blockSource.weightBlock (omega phi) =
        irreducibleBrauerCharacterBlock iota hinj blocks phi) :=
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
  fun hcompat primary source values jordan zero descent blocks ordinary union literal23
      productFormula finiteBasic hseries eq35 tensorLabel tensor_character tensor_parameter
      blockSource localPhysical ambientPhysical published =>
    specialClifford_proposition_4_4_broue_michel_relative
      (parameters := parameters)
      (N := N)
      (fs := fs)
      (D := D)
      (Msys := Msys)
      (iota := iota)
      (hinj := hinj)
      (hcompat := hcompat)
      (scope := scope)
      (choice := choice)
      (primary := primary)
      (source := source)
      (values := values)
      (jordan := jordan)
      (zero := zero)
      (descent := descent)
      (blocks := blocks)
      (ordinary := ordinary)
      (union := union)
      (literal23 := literal23)
      (productFormula := productFormula)
      (hseries := hseries)
      (liftCompatible := liftCompatible)
      (eq35 := eq35)
      (liftTrivial := liftTrivial)
      (tensorLabel := tensorLabel)
      (tensor_character := tensor_character)
      (tensor_parameter := tensor_parameter)
      (radicalKernel := radicalKernel)
      (blockSource := blockSource)
      (localPhysical := localPhysical)
      (ambientPhysical := ambientPhysical)
      (published := published)
      (canonicalLift := rfl)

end ModularRep.PaperProofs.TypeBProposition44BroueMichelInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
