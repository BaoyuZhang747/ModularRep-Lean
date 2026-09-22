import ModularRep.PaperProofs.TypeBSpinStabilizer
import ModularRep.PaperProofs.TypeBRationalSeriesBasicSet
import ModularRep.PaperProofs.TypeBRationalSeriesSource
import ModularRep.PaperProofs.TypeBIntegralSeriesCertificate
import ModularRep.PaperProofs.TypeBConformalDualCarriers
import ModularRep.PaperProofs.TypeBOddPrimesProposition44Relative
import ModularRep.PrimitiveBlockAutomorphism

/-!
# The Spin part of the source-instantiated Lemma 4.2 window

The group is the norm-one subgroup of the explicit split Clifford algebra.
Blocks are literal primitive central idempotents of its modular group
algebra; the idempotent at index `b` is exactly `b.1`.  Ordinary and Brauer
labels are the repository's function-valued sets of characters.

FLZ Theorem 2.3, p. 537, remains an E2 input separately on each rational
semisimple `ell'`-series and its Broue--Michel union.  The maps indexing those
partitions and the series predicate must still be source-certified as those
literal partitions.  The E1/E2 source generator identities express actual
stable reduction.  This file combines the integral basic set and derives
inverse block support from forward generator support.

The effective outer group is `C_2 x C_f`.  It is not embedded in the group
of Spin automorphisms.  Instead, the E1 action source identifies its two
factors, on exact K_0 and literal blocks, with actual regular conjugation
and the actual Spin field action.  Compatibility of labelled generators
is explicit.  Lean derives reduction naturality from those formulas and
the checked naturality of twisting.

The endpoint proves the integral block-lattice equivalence, the actual
stabilizer's 2-hypoelementarity, and the equivariant block bijection.  No
blockwise lattice equivalence, set bijection, BAW-goodness, or iBAW predicate
is accepted as an input.  The rational-series and effective-action source
certificates retain their E1/E2/U grades until authenticated.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinConlonBlockSourceInstantiation

open ModularRep
open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IntegralBasicSetBridge
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.ConlonBasicSet
open ModularRep.PaperProofs.OddConformalProposition311Relative
open ModularRep.PaperProofs.TypeBCliffordCarriers
open ModularRep.PaperProofs.TypeBRationalSeriesBasicSet
open ModularRep.PaperProofs.TypeBRationalSeriesSource
open ModularRep.PaperProofs.TypeBIntegralSeriesCertificate
open ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter
open ModularRep.PaperProofs.TypeBOddPrimesProposition44Relative

-- These literal finite carriers and their character coefficient fields are
-- taken in Type, matching the existing single-universe Conlon library API.
variable {n p f ell : ℕ} [NeZero f]
variable {F K O k : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable {N : NormSource n F}
variable [Finite (Spin n F N)]

/-- Literal blocks of the same Spin kernel. -/
abbrev SpinBlock := LiteralPrimitiveBlock k (Spin n F N)

/-- The specified idempotent attached to a block is its subtype value. -/
def blockIdempotent (b : SpinBlock (k := k) (N := N)) : k[Spin n F N] :=
  b.1

/-- Rational semisimple `ell'`-class indices in the actual dual PCSp.
The defining-prime coprimality condition expresses semisimplicity for
elements of this finite reductive group. -/
def RationalIndex (p ell n : ℕ) (F : Type) [Field F] :=
  {s : ConjClasses (TypeBConformalDualCarriers.PCSp F n) //
    ∃ g : TypeBConformalDualCarriers.PCSp F n,
      ConjClasses.mk g = s ∧ p.Coprime (orderOf g) ∧ ell.Coprime (orderOf g)}

instance rationalIndex_fintype (p ell n : ℕ) (F : Type) [Field F] [Finite F] :
    Fintype (RationalIndex p ell n F) := by
  letI : Finite (ConjClasses (TypeBConformalDualCarriers.PCSp F n)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  unfold RationalIndex
  exact Fintype.ofFinite _

/-- The remaining E1/U rational-source binding for this literal Spin
kernel and its literal dual PCSp.  FLZ Section 3.1, pp. 541--542, supplies
the duality; Section 2.3, pp. 536--537, fixes rational Lusztig series and
the Broue--Michel block union. `family.rationalSeries s` must be exactly
that rational series, and `blockSeries b` its Broue--Michel index.
Neither meaning is established merely by constructing this record.
There is no freely chosen dual carrier or extra Brauer partition. -/
structure SpinRationalSeriesSource where
  family : RationalSeriesSource K (Spin n F N) (RationalIndex p ell n F)
  blockSeries : SpinBlock (k := k) (N := N) → RationalIndex p ell n F

/-- The E1 algebraic-centre join uses Malle--Testerman, Proposition 9.15
and its proof, pp. 71--72, Table 9.2, p. 72, and the proof of Corollary
24.13, p. 211. For simply connected type B at odd characteristic the
algebraic centre is the order-two fundamental-group part. Its identity
component is trivial, and every automorphism of this order-two group is
trivial. Hence its Frobenius coinvariant quotient, as required in FLZ
Theorem 2.3, p. 537, has order two. FLZ Section 3.1, p. 541, fixes the
simply connected algebraic Spin model. This E1 source join is not inferred
solely from the centre of the finite-point group. The following numerical
good-prime hypotheses are proved in Lean. -/
def spinTheorem23Hypotheses
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p) :
    Theorem23Hypotheses p ell 2 where
  ell_prime := hEll
  nondefining := hNondef
  ell_odd := hOdd
  centre_primeTo := by
    intro hdiv
    have heq : 2 = ell := (Nat.prime_two.dvd_iff_eq hEll.ne_one).mp hdiv
    rcases hOdd with ⟨j, hj⟩
    omega

/-- Choose the one-way FLZ Theorem 2.3 packet only after its numerical
hypotheses, with Spin's centre-component coinvariant order fixed to two.
The global basic set is derived by finite-series aggregation. -/
def spinBasicSetFromTheorem23
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (certificate : Theorem23Certificate Msys iota hcompat hinj source.family
      blocks source.blockSeries p 2)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p) :=
  IntegralSeriesData.globalBasicSet Msys iota hcompat hinj source.family blocks source.blockSeries
    (Theorem23Certificate.data Msys iota hcompat hinj source.family blocks source.blockSeries
      certificate (spinTheorem23Hypotheses hEll hOdd hNondef))

section EffectiveActions

variable {parameters : OddFieldParameters F p f}
variable (fieldSource : FieldActionSource n F p f parameters N)
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (series : Irr K (Spin n F N) → Prop)
variable [MulAction (TypeBSpinStabilizer.OuterGroup f) (OrdinarySeriesCarrier series)]
variable [MulAction (TypeBSpinStabilizer.OuterGroup f) (IBr iota)]
variable [MulAction (TypeBSpinStabilizer.OuterGroup f) (SpinBlock (k := k) (N := N))]
variable {decomposition : FDRepKZero K (Spin n F N) →+ FDRepKZero k (Spin n F N)}

set_option maxHeartbeats 800000 in
/-- Narrow E1/U realization of the effective outer action.  FLZ Section
3.5, p. 546, identifies the diagonal quotient with `C_2`; its kernel is
literally `Spin * Z(special Clifford)`.  The field factor uses the already
specified prime Frobenius.  Exact K_0 and block formulas use inverse
automorphisms, as required by the repository's right-action convention.
No lift from the direct product into `Aut(Spin)` is postulated. -/
structure EffectiveActionSource
    (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
      (OrdinarySeriesCarrier series) decomposition) where
  labelled : LabelledKZeroActionData (A := TypeBSpinStabilizer.OuterGroup f)
    basicSet.toRestrictedIntegralBasicSet
  diagonal : SpecialClifford n F →* TypeBSpinStabilizer.DiagonalGroup
  diagonal_surjective : Function.Surjective diagonal
  diagonal_kernel : diagonal.ker =
    SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)
  ordinary_diagonal : ∀ (g : SpecialClifford n F) (x : FDRepKZero K (Spin n F N)),
    labelled.ordinaryAction (diagonal g, 1) x =
      twistKZero (k := K)
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) x
  modular_diagonal : ∀ (g : SpecialClifford n F) (x : FDRepKZero k (Spin n F N)),
    labelled.modularAction (diagonal g, 1) x =
      twistKZero (k := k)
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) x
  ordinary_field : ∀ (e : FieldGroup f) (x : FDRepKZero K (Spin n F N)),
    labelled.ordinaryAction (1, e) x =
      twistKZero (k := K) (spinFieldAction n F fieldSource e⁻¹) x
  modular_field : ∀ (e : FieldGroup f) (x : FDRepKZero k (Spin n F N)),
    labelled.modularAction (1, e) x =
      twistKZero (k := k) (spinFieldAction n F fieldSource e⁻¹) x
  block_diagonal : ∀ (g : SpecialClifford n F) (b : SpinBlock (k := k) (N := N)),
    ((diagonal g, 1) : TypeBSpinStabilizer.OuterGroup f) • b =
      LiteralPrimitiveBlock.rightTwistBlock b
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
  block_field : ∀ (e : FieldGroup f) (b : SpinBlock (k := k) (N := N)),
    ((1, e) : TypeBSpinStabilizer.OuterGroup f) • b =
      LiteralPrimitiveBlock.rightTwistBlock b (spinFieldAction n F fieldSource e⁻¹)

set_option maxHeartbeats 800000 in
/-- Naturality for the effective action is deduced from actual automorphism
naturality at its diagonal and field generators. -/
theorem reductionNatural_of_effectiveActionSource
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
      (OrdinarySeriesCarrier series)
      (decompositionMapOfStableReduction Msys iota hcompat))
    (S : EffectiveActionSource fieldSource iota hinj series basicSet) :
    DecompositionNatural (A := TypeBSpinStabilizer.OuterGroup f)
      (decompositionMapOfStableReduction Msys iota hcompat)
      S.labelled.ordinaryAction S.labelled.modularAction := by
  intro a x
  rcases a with ⟨d, e⟩
  obtain ⟨g, rfl⟩ := S.diagonal_surjective d
  have hpair : (S.diagonal g, e) =
      (S.diagonal g, (1 : FieldGroup f)) * (1, e) := by simp
  rw [hpair, map_mul, map_mul]
  change decompositionMapOfStableReduction Msys iota hcompat
      (S.labelled.ordinaryAction (S.diagonal g, 1)
        (S.labelled.ordinaryAction (1, e) x)) =
    S.labelled.modularAction (S.diagonal g, 1)
      (S.labelled.modularAction (1, e)
        (decompositionMapOfStableReduction Msys iota hcompat x))
  rw [S.ordinary_diagonal, S.ordinary_field,
    S.modular_diagonal, S.modular_field]
  rw [decompositionMapOfStableReduction_twist,
    decompositionMapOfStableReduction_twist]

end EffectiveActions

section FibreActions

variable {A X B : Type} [Group A] [MulAction A X] [MulAction A B]

/-- Stability at the actual block stabilizer follows from equivariance of
the full block map. -/
theorem stabilizerBlockStable (blockOf : X → B)
    (hequivariant : ∀ (a : A) (x : X), blockOf (a • x) = a • blockOf x)
    (b : B) (j : MulAction.stabilizer A b) (x : X) (hx : blockOf x = b) :
    blockOf (j • x) = b := by
  change blockOf ((j : A) • x) = b
  rw [hequivariant, hx]
  exact j.2

/-- The action on the literal fibre, restricted to its actual stabilizer. -/
@[instance_reducible]
def stabilizerFibreAction (blockOf : X → B)
    (hequivariant : ∀ (a : A) (x : X), blockOf (a • x) = a • blockOf x)
    (b : B) : MulAction (MulAction.stabilizer A b) (BlockFibre blockOf b) :=
  stableBlockFibreMulAction blockOf b
    (stabilizerBlockStable blockOf hequivariant b)

end FibreActions

set_option maxHeartbeats 1000000 in
/-- The Spin conclusion of Lemma 4.2, conditional only on the explicit
source inputs described above.  The rational-series input is given one
series at a time, and its reduction identity is given on generators.
The full inverse-support and blockwise equivalence are constructed. -/
theorem lemma_4_3_spin_source_instantiated
    (rank_at_least_three : 3 ≤ n)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    {parameters : OddFieldParameters F p f}
    (fieldSource : FieldActionSource n F p f parameters N)
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Finite source.family.Basic]
    [MulAction (TypeBSpinStabilizer.OuterGroup f) source.family.Basic]
    [MulAction (TypeBSpinStabilizer.OuterGroup f) (IBr iota)]
    [MulAction (TypeBSpinStabilizer.OuterGroup f) (SpinBlock (k := k) (N := N))]
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (certificate : Theorem23Certificate Msys iota hcompat hinj source.family
      blocks source.blockSeries p 2)
    (ordinaryBlock : source.family.Basic → SpinBlock (k := k) (N := N))
    (forwardGenerator : ∀ x : source.family.Basic,
      (spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
        certificate hEll hOdd hNondef).linearEquiv (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet (irreducibleBrauerCharacterBlock iota hinj blocks) (ordinaryBlock x)))
    (ordinaryBlockEquivariant : ∀ (a : TypeBSpinStabilizer.OuterGroup f)
        (x : source.family.Basic), ordinaryBlock (a • x) = a • ordinaryBlock x)
    (brauerBlockEquivariant : ∀ (a : TypeBSpinStabilizer.OuterGroup f) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (a • phi) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks phi)
    (actions : EffectiveActionSource fieldSource iota hinj source.family.selectedSeries
      (spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
        certificate hEll hOdd hNondef))
    (b : SpinBlock (k := k) (N := N))
    (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) b))
    (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) b)) :
    let J := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) b
    let _ : MulAction J (BlockFibre ordinaryBlock b) :=
      stabilizerFibreAction ordinaryBlock ordinaryBlockEquivariant b
    let _ : MulAction J
        (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks)
        brauerBlockEquivariant b
    IsPHypoelementary 2 J ∧
      Nonempty ((Representation.ofMulAction ℤ J (BlockFibre ordinaryBlock b)).Equiv
        (Representation.ofMulAction ℤ J
          (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
          BlockFibre ordinaryBlock b,
        ∀ (j : J) (phi : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b),
          e (j • phi) = j • e phi := by
  dsimp only
  let A := TypeBSpinStabilizer.OuterGroup f
  let J := MulAction.stabilizer A b
  let basicSet := spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
    certificate hEll hOdd hNondef
  have hdiagonal : BlockDiagonalLinearEquiv ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks) basicSet.linearEquiv :=
    blockDiagonalLinearEquiv_of_generator_support ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      basicSet.linearEquiv forwardGenerator
  have ambientNatural := reductionNatural_of_effectiveActionSource
    fieldSource iota hinj source.family.selectedSeries Msys hcompat basicSet actions
  have hBasic : ∀ (j : J) (x : source.family.Basic),
      j • x = (j : A) • x := fun _ _ => rfl
  have hBrauer : ∀ (j : J) (phi : IBr iota), j • phi = (j : A) • phi :=
    fun _ _ => rfl
  let restrictedActions := restrictLabelledKZeroActionDataToSubgroup
    basicSet actions.labelled J hBasic hBrauer
  have restrictedNatural := decompositionNatural_restrict_subgroup
    basicSet actions.labelled ambientNatural J hBasic hBrauer
  let ordinaryStable := stabilizerBlockStable ordinaryBlock ordinaryBlockEquivariant b
  let brauerStable := stabilizerBlockStable
    (irreducibleBrauerCharacterBlock iota hinj blocks) brauerBlockEquivariant b
  letI : MulAction J (BlockFibre ordinaryBlock b) :=
    stabilizerFibreAction ordinaryBlock ordinaryBlockEquivariant b
  letI : MulAction J
      (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
    stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks)
      brauerBlockEquivariant b
  let restricted := restrictRestrictedIntegralBasicSet
    basicSet.toRestrictedIntegralBasicSet ordinaryBlock
    (irreducibleBrauerCharacterBlock iota hinj blocks) hdiagonal b
  have hOrdinaryAction : BlockFibreActionCompatible (A := J) ordinaryBlock b :=
    fun _ _ => rfl
  have hBrauerAction : BlockFibreActionCompatible (A := J)
      (irreducibleBrauerCharacterBlock iota hinj blocks) b := fun _ _ => rfl
  have hmatrix : MatrixEquivariant (A := J) restricted.linearEquiv.toLinearMap :=
    matrixEquivariant_restrictBlock_of_kZero_naturality
      basicSet.toRestrictedIntegralBasicSet hdiagonal restrictedActions restrictedNatural
      hOrdinaryAction hBrauerAction
  let lattice := permutationLatticeEquiv restricted.linearEquiv hmatrix
  have hset := proposition_3_11_relative
    (J := J) iota hinj blocks b basicSet ordinaryBlock hdiagonal
    restrictedActions restrictedNatural ordinaryStable brauerStable
    (TypeBSpinStabilizer.fieldProjection J).ker
    (TypeBSpinStabilizer.fieldProjection_kernel_card_le_two J)
    (TypeBSpinStabilizer.quotientFieldEmbedding J)
    (TypeBSpinStabilizer.quotientFieldEmbedding_injective J) conlon burnside
  exact ⟨TypeBSpinStabilizer.spin_stabilizer_twoHypoelementary J, ⟨lattice⟩, hset⟩

end ModularRep.PaperProofs.TypeBSpinConlonBlockSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
