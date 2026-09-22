import ModularRep.PaperProofs.TypeBConlonPhysicalActionInstantiation
import ModularRep.PaperProofs.TypeBSpecialCliffordBroueMichelSource
import ModularRep.PaperProofs.TypeBFLZModularRootBinding
import ModularRep.PaperProofs.TypeBModularLinearCharacterLift
import ModularRep.BrauerCharacterSeparation

/-!
# Lemma 4.2 from the same Jordan family and specified Broue--Michel unions

The actual modular root and ordinary tensor lift are constructed from the
same modular system and prescribed cyclotomic choice. Specified block actions,
the semisimple block index, integral aggregation and support are derived.
Same-block parameter conjugacy uses the full Broue--Michel unions, without
core labels or a block-classification equivalence. The unchanged relative
Conlon--Burnside deduction supplies the blockwise conclusion.

Published clauses remain explicit on one jointly selected authentic Jordan
assignment; an arbitrary tuple is not thereby authenticated. No blockwise
bijection, global basic set, or numbered target predicate is supplied.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonBroueMichelInstantiation

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

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)
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

include union literal23 in
/-- The actual stabilizer, permutation lattice and blockwise character
bijection follow from the same published family and full block unions. -/
theorem specialClifford_lemma_4_3_broue_michel_relative
    (productFormula : BrauerLinearTensorProductFormula iota)
    [Finite (jordan.toEquation34 zero descent).rationalSeriesSource.Basic]
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
  classical
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
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
  let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b
  let bi := TypeBSpecialCliffordBroueMichelSource.blockSeries
    Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary union
  let source23 := TypeBSpecialCliffordBroueMichelSource.toTheorem23Certificate
    Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary union hcompat literal23
  let data : IntegralSeriesData Msys iota hcompat hinj
      (jordan.toEquation34 zero descent).rationalSeriesSource blocks bi :=
    Classical.choice (source23.applies
      (TypeBConlonBlockFLZSplitting.theorem23Hypotheses (jordan.toEquation34 zero descent).hypotheses))
  let basic := data.globalBasicSet Msys iota hcompat hinj (jordan.toEquation34 zero descent).rationalSeriesSource blocks bi
  let d := basic.linearEquiv
  have forwardSupport := TypeBOrdinaryBlockSplitting.forwardSupport
    Msys iota hinj blocks ordinary hcompat (jordan.toEquation34 zero descent).rationalSeriesSource bi data
  have brauer_nonempty := TypeBConlonJordanSourceInstantiation.brauerFibre_nonempty
    Msys iota hinj blocks (jordan.toEquation34 zero descent).ordinary_roots ordinary b
  have hdiag := blockDiagonalLinearEquiv_of_generator_support
    (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock)
    (irreducibleBrauerCharacterBlock iota hinj blocks) d forwardSupport
  have hX := nonempty_of_integral_lattice_equiv
    (restrictBlockLinearEquiv _ _ d hdiag b) brauer_nonempty
  obtain ⟨x⟩ := hX
  obtain ⟨l, hl⟩ := (jordan.toEquation34 zero descent).familyCharacter_surjective x.1
  have hlb : ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock ((jordan.toEquation34 zero descent).familyCharacter l) = b :=
    hl ▸ x.2
  let ambient := TypeBSpecialCliffordActionSplitting.labelledKZeroActionData
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D Msys iota hcompat hinj
    productFormula (jordan.toEquation34 zero descent).rationalSeriesSource blocks bi data hseries
  let restricted := restrictLabelledKZeroActionDataToSubgroup basic ambient J
    (fun _ _ => rfl) (fun _ _ => rfl)
  have hnatural := decompositionNatural_restrict_subgroup basic ambient
    (TypeBSpecialCliffordActionSplitting.decompositionNatural (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D Msys iota hcompat productFormula
      liftCompatible) J (fun _ _ => rfl) (fun _ _ => rfl)
  have hOrd : ∀ (a : (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))) (x : OrdinarySeriesCarrier ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries)),
      ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock (a • x) =
        a • ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock x :=
    TypeBSpecialCliffordActionSplitting.ordinarySeriesBlockMap_equivariant (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock
      hseries hOrdBlock
  have hOrdStable : ∀ (j : J) x,
      ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock x = b →
        ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock (j • x) = b := by
    intro j x hx
    change ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock (j.1 • x) = b
    rw [hOrd, hx]
    exact j.2
  have hBrStable : ∀ (j : J) phi,
      irreducibleBrauerCharacterBlock iota hinj blocks phi = b →
        irreducibleBrauerCharacterBlock iota hinj blocks (j • phi) = b := by
    intro j phi hphi
    change irreducibleBrauerCharacterBlock iota hinj blocks (j.1 • phi) = b
    rw [hBrBlock, hphi]
    exact j.2
  let tensorAction := LinearCharactersTrivialOn.fieldAction (k := k) fs.action
    (TypeCConformalActionAdapter.FieldInvariantSubgroup.isFieldStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
  let proj := TypeBBlockLabelConjugacy.fieldProjection tensorAction J
  let scalar := equation35Scalar (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D eq35 liftTrivial
  let scalarD := TypeBBlockLabelConjugacy.kernelScalar tensorAction J scalar
  have hscalar := TypeBBlockLabelConjugacy.kernelScalar_injective tensorAction J scalar
    (equation35Scalar_injective (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D eq35 liftTrivial)
  have hconj : ∀ a : proj.ker,
      IsConj l.1.1 (TypeBConformalDualCarriers.scalar F n (scalarD a) * l.1.1) := by
    intro a
    let c := TypeBBlockLabelConjugacy.kernelTensor tensorAction J a
    have hb : ordinarySeriesBlockMap (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock
        ((jordan.toEquation34 zero descent).familyCharacter (tensorLabel c l)) = b := by
      let blockOf := ordinarySeriesBlockMap
        (jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries
        (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock
      let actor : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs) := SemidirectProduct.inl c
      have h1 := congrArg blockOf (tensor_character c l)
      have h2 := hOrd actor ((jordan.toEquation34 zero descent).familyCharacter l)
      have h3 := congrArg
        (fun bb : LiteralPrimitiveBlock k (SpecialClifford n F) => actor • bb) hlb
      have h4 := congrArg
        (fun j : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
            (field_spinSubgroup_map n F fs) => j • b)
        (TypeBBlockLabelConjugacy.kernel_eq_inl tensorAction J a).symm
      exact h1.trans (h2.trans (h3.trans (h4.trans a.1.2)))
    have hc := TypeBSpecialCliffordBroueMichelSource.family_parameters_isConj_of_same_block
      Msys iota hinj (jordan.toEquation34 zero descent) blocks ordinary union l (tensorLabel c l) (hlb.trans hb.symm)
    simpa only [tensor_parameter, scalarD, TypeBBlockLabelConjugacy.kernelScalar,
      scalar, map_inv, c] using hc
  have hsmall : Nat.card proj.ker ≤ 2 := natCard_le_two_of_units_square_one
    scalarD hscalar (scalar_square_one_of_translated_conjugate scalarD
      (l.1.1) (TypeBConformalDualCarriers.translate F n)
      (TypeBConformalDualCarriers.multiplier F n) IsConj
      (TypeBConformalDualCarriers.multiplier_eq_of_isConj F n) hconj
      (TypeBConformalDualCarriers.multiplier_translate F n))
  let quotientEmbedding := proj.range.subtype.comp
    (QuotientGroup.quotientKerEquivRange proj).toMonoidHom
  have hquotient : Function.Injective quotientEmbedding := proj.range.subtype_injective.comp
    (QuotientGroup.quotientKerEquivRange proj).injective
  have hhypo := ModularRep.ManuscriptVerification.ConlonStabilizerBridge.isTwoHypoelementary_of_small_normal_quotient_embedding proj.ker hsmall
      quotientEmbedding hquotient
  have hresult := lemma_4_3_relative iota hinj blocks b basic
    (ordinarySeriesBlockMap ((jordan.toEquation34 zero descent).rationalSeriesSource.selectedSeries) (ordinary.physical (ordinaryRoots := (jordan.toEquation34 zero descent).ordinary_roots)).ordinaryBlock) hdiag restricted hnatural hOrdStable
    hBrStable proj scalarD hscalar (l.1.1)
    (TypeBConformalDualCarriers.translate F n) (TypeBConformalDualCarriers.multiplier F n)
    IsConj (TypeBConformalDualCarriers.multiplier_eq_of_isConj F n) hconj
    (TypeBConformalDualCarriers.multiplier_translate F n) conlon burnside
  exact ⟨hhypo, hresult⟩

/-- Concrete application with the SAME constructed root, Brauer separation
and entire ell-prime ordinary quotient-character lift. Leading local bindings
keep source elaboration within the default budget. The relative theorem
above is the same BM-to-Conlon deduction; no target is an input. -/
theorem specialClifford_lemma_4_3_broue_michel_instantiated :
    let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
    let hinj : IrreducibleBrauerCharacterInjectivity iota := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let liftTrivial := TypeBModularLinearCharacterLift.liftTrivial iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
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
    (b : LiteralPrimitiveBlock k (SpecialClifford n F)) ,
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
        ∀ (j : J) phi, e (j • phi) = j • e phi :=
  let iota := TypeBFLZModularRootBinding.cliffordRoot Msys choice
  let hinj : IrreducibleBrauerCharacterInjectivity iota := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let D := TypeBModularLinearCharacterLift.ordinaryReductionEquiv iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let liftCompatible := TypeBModularLinearCharacterLift.liftCompatible iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  let liftTrivial := TypeBModularLinearCharacterLift.liftTrivial iota (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  fun hcompat primary source values jordan zero descent blocks ordinary union literal23 productFormula finiteBasic hseries eq35 tensorLabel tensor_character tensor_parameter b =>
    specialClifford_lemma_4_3_broue_michel_relative
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
      (b := b)

end ModularRep.PaperProofs.TypeBConlonBroueMichelInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
