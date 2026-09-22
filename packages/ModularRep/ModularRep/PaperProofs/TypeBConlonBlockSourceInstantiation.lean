import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.PaperProofs.TypeBConformalDualCarriers
import ModularRep.PaperProofs.TypeBBlockLabelConjugacy
import ModularRep.PaperProofs.TypeBRationalSeriesBasicSet
import ModularRep.PaperProofs.TypeBOddPrimesProposition44Relative
import ModularRep.PrimitiveBlockAutomorphism

/-!
# The special Clifford part of current Lemma 4.2 on fixed carriers

The ambient group below is the even Clifford-unit normalizer of the fixed
split form, its Spin subgroup is the kernel of the literal reversal norm,
and its dual is the fixed-form CSp group. Blocks are primitive central
idempotents themselves; the indexed idempotent is definitionally the value
of that subtype. The acting group and its block stabilizer are constructed
from quotient linear characters and the source-characterized Frobenius.

The external boundary is explicit: rational Lusztig series and their
Broue--Michel partition, the individual FLZ Theorem 2.3 integral maps,
ordinary labels/core pairs from FLZ Theorem 6.3, equation (3.5), Lemma 3.6,
and standard reduction and block-support facts. Unmatched source meanings
remain U; this is a conditional endpoint, not an unconditional literature
certificate. No blockwise lattice equivalence or set bijection is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonBlockSourceInstantiation

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero IntegralBasicSetBridge OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBOddPrimesProposition44Relative
open TypeBConlonBlockRelative ConlonBasicSet OddConformalProposition311Relative

universe u

/-- A nonempty modular fibre and an integral basic-set isomorphism give a
nonempty ordinary fibre. Thus the character selected in the manuscript's
scalar argument is derived, rather than an extra basic-set assertion. -/
theorem nonempty_of_integral_lattice_equiv {X Y : Type u}
    (e : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y) (hY : Nonempty Y) :
    Nonempty X := by
  classical
  by_contra hX
  let : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
  obtain ⟨y⟩ := hY
  have hz : e.symm (MonoidAlgebra.single y (1 : ℤ)) = 0 := by
    ext x
    exact isEmptyElim x
  have h := congrArg (fun v : MonoidAlgebra ℤ X => (e v).coeff y) hz
  simpa using h

/-- Rational semisimple ell-prime classes in the actual CSp dual. In a
finite reductive group, semisimple means defining-prime regular. -/
def RationalIndex (p ell n : ℕ) (F : Type u) [Field F] :=
  {s : ConjClasses (TypeBConformalDualCarriers.CSp F n) //
    ∃ g : TypeBConformalDualCarriers.CSp F n,
      ConjClasses.mk g = s ∧ p.Coprime (orderOf g) ∧ ell.Coprime (orderOf g)}

instance rationalIndex_fintype {p ell n : ℕ} {F : Type u} [Field F] [Finite F] :
    Fintype (RationalIndex p ell n F) := by
  letI : Finite (ConjClasses (TypeBConformalDualCarriers.CSp F n)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  unfold RationalIndex
  exact Fintype.ofFinite _

section ScalarCorrespondence

variable {K k M E F : Type u}
variable [Field K] [Field k] [Field F] [Group M] [Finite M] [Group E]
variable (G0 : Subgroup M) [G0.Normal] (field : E →* MulAut M)
variable (hinvariant : TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant
  G0 field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)

/-- Equation (3.5) is used on all ordinary quotient characters; the
root-compatible lift selects its ell-prime part. -/
def equation35Scalar
    (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) G0)
    (liftTrivial : ∀ c : TensorCharacters (k := k) G0,
      TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D c ∈
          linearCharactersTrivialOn (k := K) G0)
    (c : TensorCharacters (k := k) G0) : Fˣ :=
  eq35.symm ⟨TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
    (G0 := G0) (field := field) (hinvariant := hinvariant) D c, liftTrivial c⟩

theorem equation35Scalar_injective
    (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) G0)
    (liftTrivial : ∀ c : TensorCharacters (k := k) G0,
      TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D c ∈
          linearCharactersTrivialOn (k := K) G0) :
    Function.Injective (equation35Scalar G0 field hinvariant D eq35 liftTrivial) := by
  intro c d h
  have hh := congrArg Subtype.val (eq35.symm.injective h)
  apply D.ordinaryToBrauer.symm.injective
  exact Subtype.ext hh

end ScalarCorrespondence

section LiteralSpecialClifford

variable {p ell f n : ℕ} {F K O k CharacterLabel BlockLabel : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f]
variable [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)


variable (D : OrdinaryReductionEquiv (k := k) (K := K) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable [Finite (TensorCharacters (k := k) (SpinSubgroup n F N))] [Finite (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))] [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))] [MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable [MulAction (TypeBConformalDualCarriers.CSp F n) BlockLabel]

/-- The fixed-carrier, source-instantiated special Clifford endpoint.
`perSeries` has the per-rational-series scope of FLZ Theorem 2.3, and its
generator identity binds it to the exact stable-reduction map. The
ordinary and Broue--Michel index maps remain explicit source bindings.
Theorem 6.3 and Lemma 3.6 are consumed through separate label clauses.
-/
theorem specialClifford_lemma_4_3
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (series : Irr K (SpecialClifford n F) → Prop) [Finite (OrdinarySeriesCarrier series)]
    (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D series)
    (ordinaryIndex : OrdinarySeriesCarrier series → RationalIndex p ell n F)
    (brauerIndex : IBr iota → RationalIndex p ell n F)
    (perSeries : ∀ s : RationalIndex p ell n F,
      MonoidAlgebra ℤ (SeriesFibre ordinaryIndex s) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (SeriesFibre brauerIndex s))
    (sourceGenerator : ∀ s (x : SeriesFibre ordinaryIndex s),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (seriesInclusion brauerIndex s (perSeries s (MonoidAlgebra.single x 1))) =
        decompositionMapOfStableReduction Msys iota hcompat
          (simpleClassToFDRepKZeroGenerator (ordinarySeriesLabel (K := K) series x.1)))
    (blocks : BlockIdempotentDecomposition (fun b : (LiteralPrimitiveBlock k (SpecialClifford n F)) => b.1))
    (ordinaryBlock : Irr K (SpecialClifford n F) → (LiteralPrimitiveBlock k (SpecialClifford n F)))
    (hOrdBlock : TypeCConformalActionAdapter.OrdinaryBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ordinaryBlock)
    (hBrBlock : TypeCConformalActionAdapter.BrauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks))
    (forwardSupport : ∀ x : OrdinarySeriesCarrier series,
      aggregateLinearEquiv ordinaryIndex brauerIndex perSeries (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet (irreducibleBrauerCharacterBlock iota hinj blocks)
            (ordinarySeriesBlockMap series ordinaryBlock x)))
    (liftCompatible : OrdinaryLiftReductionCompatible (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D iota)
    (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))
    (liftTrivial : ∀ c : (TensorCharacters (k := k) (SpinSubgroup n F N)),
      TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
        (G0 := (SpinSubgroup n F N)) (field := fs.action) (hinvariant := (field_spinSubgroup_map n F fs)) D c ∈
          linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))
    (b : (LiteralPrimitiveBlock k (SpecialClifford n F)))
    (brauer_nonempty : Nonempty
      (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))
    (labels : TypeBBlockLabelConjugacy.BlockLabelSource
      (Dual := (TypeBConformalDualCarriers.CSp F n)) (CharacterLabel := CharacterLabel) (BlockLabel := BlockLabel)
      (ordinarySeriesBlockMap series ordinaryBlock))
    (tensorLabel : (TensorCharacters (k := k) (SpinSubgroup n F N)) → CharacterLabel → CharacterLabel)
    (tensor_character : ∀ c l,
      labels.character (tensorLabel c l) =
        @SMul.smul (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (OrdinarySeriesCarrier series)
          (ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D series hseries).toSMul
          (SemidirectProduct.inl c) (labels.character l))
    (tensor_parameter : ∀ c l,
      labels.characterParameter (tensorLabel c l) =
        TypeBConformalDualCarriers.scalar F n
          (equation35Scalar (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D eq35 liftTrivial c)⁻¹ *
            labels.characterParameter l)
    (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b))
    (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b)) :
    let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (OrdinarySeriesCarrier series) :=
      ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D series hseries
    let _ : MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) (IBr iota) :=
      brauerCharacterAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
    let _ : MulAction J (BlockFibre (ordinarySeriesBlockMap series ordinaryBlock) b) := ordinaryBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D series ordinaryBlock b
      hseries hOrdBlock
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) := brauerBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) b hBrBlock
    IsPHypoelementary 2 J ∧
      Nonempty
        ((Representation.ofMulAction ℤ J
          (BlockFibre (ordinarySeriesBlockMap series ordinaryBlock) b)).Equiv
          (Representation.ofMulAction ℤ J
            (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
        BlockFibre (ordinarySeriesBlockMap series ordinaryBlock) b,
        ∀ (j : J) phi, e (j • phi) = j • e phi := by
  classical
  dsimp only
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D series hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
  let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b
  let d := aggregateLinearEquiv ordinaryIndex brauerIndex perSeries
  have hd := aggregate_restricts_decomposition Msys iota hcompat hinj series
    ordinaryIndex brauerIndex perSeries sourceGenerator
  let basic := ordinarySeriesBasicSet Msys iota hcompat hinj series d hd
  have hdiag := blockDiagonalLinearEquiv_of_generator_support
    (ordinarySeriesBlockMap series ordinaryBlock)
    (irreducibleBrauerCharacterBlock iota hinj blocks) d forwardSupport
  have hX := nonempty_of_integral_lattice_equiv
    (restrictBlockLinearEquiv _ _ d hdiag b) brauer_nonempty
  obtain ⟨x⟩ := hX
  obtain ⟨l, hl⟩ := labels.character_surjective x.1
  have hlb : ordinarySeriesBlockMap series ordinaryBlock (labels.character l) = b :=
    hl ▸ x.2
  let ambient := labelledKZeroActionData (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D Msys iota hcompat hinj
    productFormula series hseries d hd
  let restricted := restrictLabelledKZeroActionDataToSubgroup basic ambient J
    (fun _ _ => rfl) (fun _ _ => rfl)
  have hnatural := decompositionNatural_restrict_subgroup basic ambient
    (decompositionNatural (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D Msys iota hcompat productFormula
      liftCompatible) J (fun _ _ => rfl) (fun _ _ => rfl)
  have hOrd : ∀ (a : (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))) (x : OrdinarySeriesCarrier series),
      ordinarySeriesBlockMap series ordinaryBlock (a • x) =
        a • ordinarySeriesBlockMap series ordinaryBlock x :=
    ordinarySeriesBlockMap_equivariant (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D series ordinaryBlock
      hseries hOrdBlock
  have hOrdStable : ∀ (j : J) x,
      ordinarySeriesBlockMap series ordinaryBlock x = b →
        ordinarySeriesBlockMap series ordinaryBlock (j • x) = b := by
    intro j x hx
    change ordinarySeriesBlockMap series ordinaryBlock (j.1 • x) = b
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
  have hconj := TypeBBlockLabelConjugacy.translated_conjugate tensorAction
    (ordinarySeriesBlockMap series ordinaryBlock) hOrd labels scalar
    (TypeBConformalDualCarriers.scalar F n) tensorLabel tensor_character
    tensor_parameter b l hlb
  have hsmall : Nat.card proj.ker ≤ 2 := natCard_le_two_of_units_square_one
    scalarD hscalar (scalar_square_one_of_translated_conjugate scalarD
      (labels.characterParameter l) (TypeBConformalDualCarriers.translate F n)
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
    (ordinarySeriesBlockMap series ordinaryBlock) hdiag restricted hnatural hOrdStable
    hBrStable proj scalarD hscalar (labels.characterParameter l)
    (TypeBConformalDualCarriers.translate F n) (TypeBConformalDualCarriers.multiplier F n)
    IsConj (TypeBConformalDualCarriers.multiplier_eq_of_isConj F n) hconj
    (TypeBConformalDualCarriers.multiplier_translate F n) conlon burnside
  exact ⟨hhypo, hresult⟩

end LiteralSpecialClifford

end ModularRep.PaperProofs.TypeBConlonBlockSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
