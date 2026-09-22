import ModularRep.PaperProofs.TypeBConlonBlockSourceInstantiation
import ModularRep.PaperProofs.TypeBFLZLabelSplittingSource
import ModularRep.PaperProofs.TypeBSpecialCliffordActionSplitting

/-!
# FLZ-bound special-Clifford Lemma 4.2 over a splitting fraction field

The same FLZ equation-(3.4) labels determine the selected ordinary rational
series; the same Theorem-6.3 specified block labels determine its Brauer
series index. Individual FLZ Theorem-2.3 packets are aggregated with their
literal stable-decomposition equations. The actual tensor/field actions on
that constructed basic set come from the checked splitting-field adapter.

The block stabilizer, scalar kernel, order bound, cyclic quotient, block
restriction and Conlon--Burnside deduction are constructed below. No global
basic set, blockwise correspondence or target predicate is an input.

Source realization remains explicit: full rational-series/Broue--Michel
union identification (beyond Theorem 6.3's t=1 membership), the second
centralizer-character/core action, actual algebraic finite points and
connected centre, and the same ordinary/modular root, reduction and block
selector. The ordinary field is not required to be algebraically closed.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonBlockFLZSplitting

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
variable (unipotent : UnipotentPredicate F K p n)
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]
variable (S : Equation34Source (ell := ell) unipotent)
variable (Core : AdmissibleParameter F p ell n → Type)
variable [MulAction (CSp F n) (BlockPair F p ell n Core)]
variable (ordinaryBlock : Irr K (SpecialClifford n F) →
  LiteralPrimitiveBlock k (SpecialClifford n F))
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (T : Theorem63Source unipotent S Core ordinaryBlock iota blocks)

/-- The E1 connected-centre specialization of the numerical FLZ-2.3
hypotheses. The prime and rank scope is already fixed by equation (3.4). -/
theorem theorem23Hypotheses (scope : Applicability p ell n) : Theorem23Hypotheses p ell 1 where
  ell_prime := scope.modular_prime
  nondefining := scope.nondefining
  ell_odd := scope.modular_odd
  centre_primeTo := scope.modular_prime.not_dvd_one

instance sourceIndexFintype : Fintype (SourceIndex F p ell n) :=
  rationalIndex_fintype

variable (source23 : Theorem23Certificate Msys iota hcompat hinj
  S.rationalSeriesSource blocks T.blockSeries p 1 (ordinaryRoots := S.ordinary_roots))

/-- Exactly the packet selected by the forward Theorem-2.3 certificate. -/
def integralData : IntegralSeriesData Msys iota hcompat hinj
    S.rationalSeriesSource blocks T.blockSeries := by
  letI := S.ordinary_roots
  exact Classical.choice (source23.applies (theorem23Hypotheses S.hypotheses))

/-- The source-bound endpoint returns a hypoelementary actual stabilizer,
a permutation-lattice isomorphism, and an equivariant actual
Brauer-to-basic-set block bijection.
Only source-sized maps and compatibility formulas occur among the inputs. -/
theorem specialClifford_lemma_4_3_source_instantiated
    (productFormula : BrauerLinearTensorProductFormula iota)
    [Finite S.rationalSeriesSource.Basic]
    (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        S.rationalSeriesSource.selectedSeries)
    (hOrdBlock : TypeCConformalActionAdapter.OrdinaryBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ordinaryBlock)
    (hBrBlock : TypeCConformalActionAdapter.BrauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks))
    (forwardSupport :
      let data := integralData Msys iota hcompat hinj unipotent S Core ordinaryBlock blocks T source23
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
    let _ : MulAction J (BlockFibre (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock) b) := TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (S.rationalSeriesSource.selectedSeries) ordinaryBlock b
      hseries hOrdBlock
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) := brauerBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) b hBrBlock
    IsPHypoelementary 2 J ∧
      Nonempty
        ((Representation.ofMulAction ℤ J
          (BlockFibre (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock) b)).Equiv
          (Representation.ofMulAction ℤ J
            (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
        BlockFibre (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock) b,
        ∀ (j : J) phi, e (j • phi) = j • e phi := by
  classical
  dsimp only
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (S.rationalSeriesSource.selectedSeries) hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
  let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)) b
  let data := integralData Msys iota hcompat hinj unipotent S Core ordinaryBlock blocks T source23
  let basic := data.globalBasicSet Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries
  let d := basic.linearEquiv
  let labels := toFamilyBlockLabelSource unipotent S Core ordinaryBlock T
  have hdiag := blockDiagonalLinearEquiv_of_generator_support
    (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock)
    (irreducibleBrauerCharacterBlock iota hinj blocks) d forwardSupport
  have hX := nonempty_of_integral_lattice_equiv
    (restrictBlockLinearEquiv _ _ d hdiag b) brauer_nonempty
  obtain ⟨x⟩ := hX
  obtain ⟨l, hl⟩ := labels.character_surjective x.1
  have hlb : ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock (labels.character l) = b :=
    hl ▸ x.2
  let ambient := TypeBSpecialCliffordActionSplitting.labelledKZeroActionData
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D Msys iota hcompat hinj
    productFormula S.rationalSeriesSource blocks T.blockSeries data hseries
  let restricted := restrictLabelledKZeroActionDataToSubgroup basic ambient J
    (fun _ _ => rfl) (fun _ _ => rfl)
  have hnatural := decompositionNatural_restrict_subgroup basic ambient
    (TypeBSpecialCliffordActionSplitting.decompositionNatural (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D Msys iota hcompat productFormula
      liftCompatible) J (fun _ _ => rfl) (fun _ _ => rfl)
  have hOrd : ∀ (a : (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))) (x : OrdinarySeriesCarrier (S.rationalSeriesSource.selectedSeries)),
      ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock (a • x) =
        a • ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock x :=
    TypeBSpecialCliffordActionSplitting.ordinarySeriesBlockMap_equivariant (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (S.rationalSeriesSource.selectedSeries) ordinaryBlock
      hseries hOrdBlock
  have hOrdStable : ∀ (j : J) x,
      ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock x = b →
        ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock (j • x) = b := by
    intro j x hx
    change ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock (j.1 • x) = b
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
    (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock) hOrd labels scalar
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
    (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock) hdiag restricted hnatural hOrdStable
    hBrStable proj scalarD hscalar (labels.characterParameter l)
    (TypeBConformalDualCarriers.translate F n) (TypeBConformalDualCarriers.multiplier F n)
    IsConj (TypeBConformalDualCarriers.multiplier_eq_of_isConj F n) hconj
    (TypeBConformalDualCarriers.multiplier_translate F n) conlon burnside
  exact ⟨hhypo, hresult⟩

end ModularRep.PaperProofs.TypeBConlonBlockFLZSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
