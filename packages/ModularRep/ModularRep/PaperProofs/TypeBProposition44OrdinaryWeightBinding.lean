import ModularRep.PaperProofs.TypeBConlonBroueMichelInstantiation
import ModularRep.PaperProofs.TypeCWeightTensorFieldAction
import ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily
import ModularRep.PaperProofs.TypeBRadicalLiftKernel

/-!
# The same Jordan family's published ordinary-weight correspondence

FLZ Proposition 7.2, pp. 571--572, supplies an ordinary
`E(D_0, ell')`-to-weight-class correspondence. Its block assertion uses the
literal weights of section 5.5 and Proposition 6.7. Its tensor and field
assertions use Lemma 3.6 and Propositions 3.9, 5.15 and 7.1. The later
Assumption-3.11 Brauer replacement is not an input here.

The ordinary family below is the SAME `JordanCertificate.toEquation34`
family, with its prescribed ordinary roots and specified ordinary selector.
The local quotient, ordinary defect-zero character, inflation and block
induction remain those in `LocalBlockInductionSource`. Its fixed-root local
block guard and literal ambient catalogue allocation are explicit indices.
These are narrowly scoped specified source obligations; arbitrary catalogue
choices are not authenticated merely by satisfying a target block formula.

The only fields of the E2 packet are its ordinary map and the three
published tensor, field and block equations. Combined equivariance and
construction from orbit representatives are K. The final helper accepts already DERIVED Lemma 4.2
representative maps, outside the source packet, and invokes the checked
orbit theorem. It does not assert that those maps are published inputs or
that the full Proposition 4.3 criterion is established. No algebraic closure
of the ordinary fraction field is required.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBProposition44OrdinaryWeightBinding

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBSpecialCliffordActionAdapter TypeCWeightTensorFieldAction
open TypeBFLZLabelSource (FullCharacterPair Applicability)
open OddConlonOrbitAssembly BlockFibreRestriction

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)

local instance cliffordFintype : Fintype (SpecialClifford n F) := Fintype.ofFinite _

variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable (radicalKernel : RadicalKernelLiftInput (p := ell)
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D)
variable (Msys : ModularSystem ell K O k)
variable (scope : Applicability p ell n)
variable (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)
variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
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

variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
variable (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
  Msys iota hinj blocks (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots))
variable (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
  (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)
variable (blockSource : CharacterWeight.LocalBlockInductionSource
  (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
  (Block := LiteralPrimitiveBlock k (SpecialClifford n F)))

/-- The exact E2 ordinary correspondence on one jointly selected published
Jordan family. The local specified guard and allocation are retained as
explicit constructor indices, not inferred from the block equation.
`canonicalLift` identifies the actual tensor actor with the full published
prime-to-ell quotient-character group by the checked lift-range theorem.
`radicalKernel` is a K deduction from the prime-to-ell lift; it is not a
published weight-matching assertion. -/
structure PublishedOrdinaryWeightMap
    (canonicalLift : D = TypeBModularLinearCharacterLift.ordinaryReductionEquiv
      iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
    (localPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
      iota blockSource.operations)
    (ambientPhysical : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
      blockSource.operations.ambientBlockData.blockIdempotent b = b.val)
    [ordinaryCharacteristic : CharZero K] where
  rho : (jordan.toEquation34 zero descent).rationalSeriesSource.Basic ≃
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F)
  tensor : ∀ (c : TensorCharacters (k := k) (SpinSubgroup n F N))
      (x : (jordan.toEquation34 zero descent).rationalSeriesSource.Basic),
    rho (@SMul.smul
      (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
      (jordan.toEquation34 zero descent).rationalSeriesSource.Basic
      (ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs) D
        (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries hseries).toSMul
      (SemidirectProduct.inl c) x) =
      CharacterWeight.linearTwistConjugacyClass
        (radicalLift (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
          D radicalKernel c)⁻¹ (rho x)
  field : ∀ (e : FieldGroup f)
      (x : (jordan.toEquation34 zero descent).rationalSeriesSource.Basic),
    rho (@SMul.smul
      (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
      (jordan.toEquation34 zero descent).rationalSeriesSource.Basic
      (ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs) D
        (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries hseries).toSMul
      (SemidirectProduct.inr e) x) =
      CharacterWeight.rightTwistConjugacyClass (fs.action e⁻¹) (rho x)
  block : ∀ x : (jordan.toEquation34 zero descent).rationalSeriesSource.Basic,
    blockSource.weightBlock (rho x) =
      (ordinary.physical
        (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock x.val

variable (canonicalLift : D = TypeBModularLinearCharacterLift.ordinaryReductionEquiv
  iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable (localPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
  iota blockSource.operations)
variable (ambientPhysical : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
  blockSource.operations.ambientBlockData.blockIdempotent b = b.val)
variable (published : PublishedOrdinaryWeightMap
  (parameters := parameters) (N := N)
  (fs := fs) (D := D) (radicalKernel := radicalKernel)
  (scope := scope) (choice := choice)
  (Msys := Msys) (iota := iota) (hinj := hinj)
  (primary := primary) (source := source) (values := values)
  (jordan := jordan) (zero := zero) (descent := descent)
  (blocks := blocks) (ordinary := ordinary) (hseries := hseries)
  (blockSource := blockSource) canonicalLift localPhysical ambientPhysical)

/-- The separate source equations imply the actual combined semidirect
equivariance. Tensoring is by the inverse lift after inverse field pullback. -/
theorem combined_equivariant :
    letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D
      (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries hseries
    letI := tensorFieldSemidirectAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D radicalKernel
    ∀ (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs))
      (x : (jordan.toEquation34 zero descent).rationalSeriesSource.Basic),
      published.rho (a • x) = a • published.rho x := by
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D
    (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries hseries
  letI := tensorFieldSemidirectAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D radicalKernel
  intro a x
  have hsource : a • x =
      (SemidirectProduct.inl a.left : ActingGroup (k := k)
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) •
      ((SemidirectProduct.inr a.right : ActingGroup (k := k)
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) • x) := by
    exact (congrArg
      (fun b : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs) => b • x)
      (SemidirectProduct.mk_eq_inl_mul_inr a.right a.left)).trans
      (mul_smul _ _ x)
  exact (congrArg published.rho hsource).trans
    ((published.tensor a.left
      ((SemidirectProduct.inr a.right : ActingGroup (k := k)
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) • x)).trans
      ((congrArg
        (CharacterWeight.linearTwistConjugacyClass
          (radicalLift (SpinSubgroup n F N) fs.action
            (field_spinSubgroup_map n F fs) D radicalKernel a.left)⁻¹)
        (published.field a.right x)).trans
        (tensorFieldSemidirectAction_apply (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs) D radicalKernel a (published.rho x)).symm))

include published in
/-- Thin K construction boundary. `derivedLemma43` must be supplied by the
checked Lemma 4.2 deduction on the actual representative blocks; it is not
part of `PublishedOrdinaryWeightMap` and is not an external source clause.
Specified ordinary/Brauer block equivariance is derived with the existing
decomposition and group algebra action theorems. -/
theorem assemble_of_derived_lemma43
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (liftCompatible : OrdinaryLiftReductionCompatible
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D iota) :
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
    let ordinaryBlock := ordinarySeriesBlockMap
      (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
      (ordinary.physical
        (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock
    let brauerBlock := FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock iota hinj blocks
    let hBrBlock := TypeBPhysicalBlockAction.brauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      iota productFormula hinj blocks
    ∀ (derivedLemma43 : RepresentativeEquivExists
      brauerBlock ordinaryBlock hBrBlock),
    ∃ omega : IBr iota ≃
        CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F),
      (∀ (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (phi : IBr iota),
        omega (a • phi) = a • omega phi) ∧
      (∀ phi : IBr iota, blockSource.weightBlock (omega phi) = brauerBlock phi) := by
  dsimp only
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
  intro derivedLemma43
  have hBrBlock := TypeBPhysicalBlockAction.brauerBlockEquivariant
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    iota productFormula hinj blocks
  have hOrdFull := TypeBPhysicalDecompositionAction.ordinaryBlock_equivariant_of_brauer
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    D Msys iota hcompat hinj productFormula liftCompatible blocks ordinary hBrBlock
  have hOrdBlock := TypeBSpecialCliffordActionSplitting.ordinarySeriesBlockMap_equivariant
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
    (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
    (ordinary.physical
      (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock
    hseries hOrdFull
  exact exists_condition_ii_bijection_of_orbitwise_composition
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock iota hinj blocks)
    (ordinarySeriesBlockMap
      (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
      (ordinary.physical
        (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock)
    blockSource.weightBlock hBrBlock hOrdBlock derivedLemma43 published.rho
    (combined_equivariant (published := published)) published.block

end ModularRep.PaperProofs.TypeBProposition44OrdinaryWeightBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
