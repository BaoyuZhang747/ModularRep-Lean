import ModularRep.PaperProofs.TypeBConlonBlockFLZ
import ModularRep.PaperProofs.TypeBOddPrimesProposition44Actual
import ModularRep.PaperProofs.TypeBRadicalLiftKernel

/-!
# The source-instantiated bijection part of Type B Proposition 4.3

The carriers, equation-(3.4) family, Theorem-6.3 primitive blocks, and
individual Theorem-2.3 integral maps are the same as the accepted Lemma
4.2 window. FLZ Proposition 7.2, pp. 571--572, supplies only its ordinary
family-to-weight correspondence, its separate tensor and field formulas,
and its block formula. Weight classes are literal character weights of
the even Clifford-unit normalizer, with the local quotient and induced
block operations retained in the exact local source record.

The proof constructs the integral map and block restriction, selects a
source character label in each nonempty primitive block, and constructs
the orbit-representative field projections and scalar translations. It
then invokes the existing checked Proposition-4.4 construction from orbit representatives once.
No Brauer-to-weight bijection, goodness predicate, or iBAW criterion is an
input. The result is the block-preserving equivariant bijection; the full
criterion and unmatched local source meanings remain separate obligations.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBProposition44SourceInstantiation

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero IntegralBasicSetBridge OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesCertificate TypeBFLZLabelSource
open TypeBConlonBlockSourceInstantiation TypeBConlonBlockFLZ ConlonBasicSet
open OddConlonOrbitAssembly TypeCWeightTensorFieldAction

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)

local instance : Fintype (SpecialClifford n F) := Fintype.ofFinite _

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
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]
variable (S : Equation34Source (ell := ell) unipotent)
variable (Core : AdmissibleParameter F p ell n → Type)
variable [MulAction (CSp F n) (BlockPair F p ell n Core)]
variable (ordinaryBlock : Irr K (SpecialClifford n F) →
  LiteralPrimitiveBlock k (SpecialClifford n F))
variable (T : Theorem63Source unipotent S Core ordinaryBlock)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (source23 : Theorem23Certificate Msys iota hcompat hinj
  S.rationalSeriesSource blocks T.blockSeries p 1)
variable (seriesTensorStable : TypeCConformalActionAdapter.OrdinarySeriesTensorStable
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
    S.rationalSeriesSource.selectedSeries)
variable (seriesFieldStable : TypeCConformalActionAdapter.OrdinarySeriesFieldStable
  (K := K) fs.action S.rationalSeriesSource.selectedSeries)
variable (liftPrimeTo : ∀ c : TensorCharacters (k := k) (SpinSubgroup n F N),
  ell.Coprime (orderOf (TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
    (G0 := SpinSubgroup n F N) (field := fs.action)
    (hinvariant := field_spinSubgroup_map n F fs) D c)))
variable (blockSource : CharacterWeight.LocalBlockInductionSource
  (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
  (Block := LiteralPrimitiveBlock k (SpecialClifford n F)))

/-- The E1/U specified allocation of the ambient catalogue used in local
weight-block induction. Merely indexing this catalogue by primitive
blocks would not identify its stored idempotent with the subtype value.
This equation binds it to the very same primitive idempotents used by
the global Brauer block decomposition. -/
structure LiteralBlockSourceBinding : Prop where
  ambient_idempotent : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1

set_option maxHeartbeats 1000000 in
/-- Exact E2/U carrier binding of FLZ Proposition 7.2. Its ordinary
domain is equation (3.4)'s selected rational family and its codomain is
actual weight conjugacy classes. The local block source must realize the
published local quotient, inflation, and block-induction operations on
the displayed primitive blocks. No Brauer-character conclusion occurs.
-/
structure Theorem72Source where
  rho : S.rationalSeriesSource.Basic ≃
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F)
  tensor : ∀ (c : TensorCharacters (k := k) (SpinSubgroup n F N))
      (x : S.rationalSeriesSource.Basic),
    rho (TypeBOddPrimesProposition44Actual.ordinaryTensorStep
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
      S.rationalSeriesSource.selectedSeries seriesTensorStable c x) =
      CharacterWeight.linearTwistConjugacyClass
        (radicalLift (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
          D (TypeBRadicalLiftKernel.specialCliffordRadicalKernel parameters N fs D
            liftPrimeTo) c)⁻¹ (rho x)
  field : ∀ (e : FieldGroup f) (x : S.rationalSeriesSource.Basic),
    rho (TypeBOddPrimesProposition44Actual.ordinaryFieldStep fs.action
      S.rationalSeriesSource.selectedSeries seriesFieldStable e x) =
      CharacterWeight.rightTwistConjugacyClass (fs.action e⁻¹) (rho x)
  block : ∀ x : S.rationalSeriesSource.Basic,
    blockSource.weightBlock (rho x) = ordinaryBlock x.1

set_option maxHeartbeats 1600000 in
/-- Source-instantiated global Brauer/weight bijection, using the existing
construction from orbit representatives and the literal Lemma-4.3 source data. This proves only the
stated equivariance and primitive-block preservation, not a full iBAW
criterion. Theorem-7.2's ordinary correspondence remains a separate E2
input with its literal tensor, field, and block formulas. -/
theorem proposition_4_4_source_instantiated
    (productFormula : BrauerLinearTensorProductFormula iota)
    [Finite S.rationalSeriesSource.Basic]
    (hOrdBlock : TypeCConformalActionAdapter.OrdinaryBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ordinaryBlock)
    (hBrBlock : TypeCConformalActionAdapter.BrauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks))
    (forwardSupport :
      let data := integralData Msys iota hcompat hinj unipotent S Core ordinaryBlock T
        blocks source23
      ∀ x : S.rationalSeriesSource.Basic,
        aggregateLinearEquiv S.rationalSeriesSource.ordinaryIndex
          (brauerIndex iota hinj blocks T.blockSeries)
          (data.fibreMaps Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries)
          (MonoidAlgebra.single x 1) ∈ MonoidAlgebra.supported ℤ ℤ
            (blockFibreSet (irreducibleBrauerCharacterBlock iota hinj blocks)
              (ordinaryBlock x.1)))
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
    (tensor_character :
      let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        S.rationalSeriesSource.selectedSeries seriesTensorStable seriesFieldStable
      ∀ c l, S.familyCharacter (tensorLabel c l) =
        @SMul.smul (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) S.rationalSeriesSource.Basic
          (ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
            (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries
            hseries).toSMul (SemidirectProduct.inl c) (S.familyCharacter l))
    (tensor_parameter : ∀ c l,
      (tensorLabel c l).1.1 = scalar F n
        (equation35Scalar (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs) D eq35 liftTrivial c)⁻¹ * l.1.1)
    (brauer_nonempty : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
      Nonempty (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))
    (conlon : ∀ orbit : BlockOrbit
        (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (orbitRepresentative orbit)))
    (burnside : ∀ orbit : BlockOrbit
        (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (orbitRepresentative orbit)))
    (blockBinding : LiteralBlockSourceBinding blockSource)
    (source72 : Theorem72Source parameters N fs D unipotent S ordinaryBlock
      seriesTensorStable seriesFieldStable liftPrimeTo blockSource) :
    let A := ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)
    let _ : MulAction A (IBr iota) := brauerCharacterAction (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs) iota productFormula
    let _ : MulAction A
        (CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F)) :=
      TypeBOddPrimesProposition44Actual.weightAction (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs) D
        (TypeBRadicalLiftKernel.specialCliffordRadicalKernel parameters N fs D liftPrimeTo)
    ∃ omega : IBr iota ≃
        CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F),
      (∀ (a : A) (phi : IBr iota), omega (a • phi) = a • omega phi) ∧
      (∀ phi : IBr iota, blockSource.weightBlock (omega phi) =
        irreducibleBrauerCharacterBlock iota hinj blocks phi) ∧
      (∀ (a : A)
          (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F)),
        blockSource.weightBlock (a • W) = a • blockSource.weightBlock W) := by
  classical
  dsimp only
  let A := ActingGroup (k := k) (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs)
  let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
    S.rationalSeriesSource.selectedSeries seriesTensorStable seriesFieldStable
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) iota productFormula
  letI := TypeBOddPrimesProposition44Actual.weightAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D
    (TypeBRadicalLiftKernel.specialCliffordRadicalKernel parameters N fs D liftPrimeTo)
  let data := integralData Msys iota hcompat hinj unipotent S Core ordinaryBlock T
    blocks source23
  let d := aggregateLinearEquiv S.rationalSeriesSource.ordinaryIndex
    (brauerIndex iota hinj blocks T.blockSeries)
    (data.fibreMaps Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries)
  have hd := aggregate_restricts_decomposition Msys iota hcompat hinj
    S.rationalSeriesSource.selectedSeries S.rationalSeriesSource.ordinaryIndex
    (brauerIndex iota hinj blocks T.blockSeries)
    (data.fibreMaps Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries)
    (data.fibreGenerator Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries)
  have hdiag := blockDiagonalLinearEquiv_of_generator_support
    (ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries ordinaryBlock)
    (irreducibleBrauerCharacterBlock iota hinj blocks) d forwardSupport
  let labels := toFamilyBlockLabelSource unipotent S Core ordinaryBlock T
  have labelExists : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
      ∃ l : CharacterPair F K p ell n unipotent,
        ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries ordinaryBlock
          (labels.character l) = b := by
    intro b
    obtain ⟨x⟩ := nonempty_of_integral_lattice_equiv
      (restrictBlockLinearEquiv _ _ d hdiag b) (brauer_nonempty b)
    obtain ⟨l, hl⟩ := labels.character_surjective x.1
    exact ⟨l, hl ▸ x.2⟩
  choose label labelBlock using labelExists
  have hOrd : ∀ (a : A) (x : S.rationalSeriesSource.Basic),
      ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries ordinaryBlock (a • x) =
        a • ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries ordinaryBlock x :=
    ordinarySeriesBlockMap_equivariant (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries ordinaryBlock
      hseries hOrdBlock
  let tensorAction := LinearCharactersTrivialOn.fieldAction (k := k) fs.action
    (TypeCConformalActionAdapter.FieldInvariantSubgroup.isFieldStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
  let projection := fun orbit : BlockOrbit A (LiteralPrimitiveBlock k (SpecialClifford n F)) =>
    TypeBBlockLabelConjugacy.fieldProjection tensorAction
      (MulAction.stabilizer A (orbitRepresentative orbit))
  let quotientScalar := equation35Scalar (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D eq35 liftTrivial
  let scalarD := fun orbit : BlockOrbit A (LiteralPrimitiveBlock k (SpecialClifford n F)) =>
    TypeBBlockLabelConjugacy.kernelScalar tensorAction
      (MulAction.stabilizer A (orbitRepresentative orbit)) quotientScalar
  have hscalar : ∀ orbit, Function.Injective (scalarD orbit) := by
    intro orbit
    exact TypeBBlockLabelConjugacy.kernelScalar_injective tensorAction
      (MulAction.stabilizer A (orbitRepresentative orbit)) quotientScalar
      (equation35Scalar_injective (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs) D eq35 liftTrivial)
  let parameter := fun orbit : BlockOrbit A (LiteralPrimitiveBlock k (SpecialClifford n F)) =>
    labels.characterParameter (label (orbitRepresentative orbit))
  have hconj : ∀ orbit (z : (projection orbit).ker),
      IsConj (parameter orbit) (translate F n (scalarD orbit z) (parameter orbit)) := by
    intro orbit
    exact TypeBBlockLabelConjugacy.translated_conjugate tensorAction
      (ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries ordinaryBlock) hOrd
      labels quotientScalar (scalar F n) tensorLabel tensor_character tensor_parameter
      (orbitRepresentative orbit) (label (orbitRepresentative orbit))
      (labelBlock (orbitRepresentative orbit))
  exact TypeBOddPrimesProposition44Actual.proposition_4_4_global_weight_equiv_actual
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
    Msys iota hcompat hinj productFormula S.rationalSeriesSource.selectedSeries
    seriesTensorStable seriesFieldStable d hd ordinaryBlock hOrdBlock blocks hBrBlock hdiag
    liftCompatible (TypeBRadicalLiftKernel.specialCliffordRadicalKernel parameters N fs D
      liftPrimeTo) projection scalarD hscalar parameter (translate F n)
    (multiplier F n) IsConj (multiplier_eq_of_isConj F n) hconj
    (multiplier_translate F n) conlon burnside blockSource source72.rho
    source72.tensor source72.field source72.block

end ModularRep.PaperProofs.TypeBProposition44SourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
