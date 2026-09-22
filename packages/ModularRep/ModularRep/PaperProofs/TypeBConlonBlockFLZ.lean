import ModularRep.PaperProofs.TypeBConlonBlockSourceInstantiation
import ModularRep.PaperProofs.TypeBFLZLabelSource
import ModularRep.PaperProofs.TypeBIntegralSeriesCertificate

/-!
# The FLZ-bound special Clifford window of Lemma 4.2

The equation-(3.4) family supplies both the literal ordinary carrier and
its rational-series index. Theorem 6.3 supplies the primitive-block index.
The latter is composed with the actual Brauer block assignment. Thus the
individual Theorem-2.3 maps, ordinary labels, and block labels use the same
semisimple classes. Theorem 2.3 is consumed only forward at centre order
one, the E1 algebraic-centre specialization for D0 (connected Gm centre).

Unipotent/core definitions and their source realizations remain explicit
in the source records. No blockwise bijection is an external input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonBlockFLZ

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero IntegralBasicSetBridge OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesCertificate TypeBFLZLabelSource
open TypeBConlonBlockSourceInstantiation ConlonBasicSet

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
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
variable (T : Theorem63Source unipotent S Core ordinaryBlock)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))

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
  S.rationalSeriesSource blocks T.blockSeries p 1)

/-- Exactly the packet selected by the forward Theorem-2.3 certificate. -/
def integralData : IntegralSeriesData Msys iota hcompat hinj
    S.rationalSeriesSource blocks T.blockSeries :=
  source23.data Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries
    (theorem23Hypotheses S.hypotheses)

/-- The source-bound endpoint. Its exact proposition is printed in the
Type B axiom audit: a hypoelementary actual stabilizer, a permutation-lattice
isomorphism, and an equivariant actual Brauer-to-basic-set block bijection.
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
    let _ : MulAction J (BlockFibre (ordinarySeriesBlockMap (S.rationalSeriesSource.selectedSeries) ordinaryBlock) b) := ordinaryBlockFibreAction (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D (S.rationalSeriesSource.selectedSeries) ordinaryBlock b
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
        ∀ (j : J) phi, e (j • phi) = j • e phi :=
  specialClifford_lemma_4_3 parameters N fs D Msys iota hcompat hinj productFormula
    S.rationalSeriesSource.selectedSeries hseries S.rationalSeriesSource.ordinaryIndex
    (brauerIndex iota hinj blocks T.blockSeries)
    ((integralData Msys iota hcompat hinj unipotent S Core ordinaryBlock T blocks source23).fibreMaps Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries)
    ((integralData Msys iota hcompat hinj unipotent S Core ordinaryBlock T blocks source23).fibreGenerator Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries)
    blocks ordinaryBlock hOrdBlock hBrBlock forwardSupport liftCompatible eq35 liftTrivial
    b brauer_nonempty (toFamilyBlockLabelSource unipotent S Core ordinaryBlock T)
    tensorLabel tensor_character tensor_parameter conlon burnside

end ModularRep.PaperProofs.TypeBConlonBlockFLZ


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
