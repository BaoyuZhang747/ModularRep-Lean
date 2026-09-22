import ModularRep.PaperProofs.TypeBSpinConlonBlockSourceInstantiation
import ModularRep.PaperProofs.TypeBIntegralSeriesSplitting

/-!
# Spin Lemma 4.2 with a consistent ordinary splitting fraction field

Reuse literal Spin/PCSp rational indices, primitive blocks, effective action
and actual stabilizer data. Replace the ordinary-label/per-series source
composition that inherited an impossible algebraically closed DVR fraction
field. Exact reduction, block restriction and checked Conlon--Burnside
deductions are retained. No resource-limit override is introduced.

FLZ Theorem 2.3 is supplied only on individual actual rational series with
literal generator reduction and sufficient ordinary roots. Algebraic
finite-point, rational-series, centre and effective-action realizations
remain explicit E1/E2/U. No blockwise equivalence, equivariant bijection
or BAW/iBAW target is an input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinConlonSplittingSourceInstantiation

open ModularRep BlockFibreRestriction DecompositionBasicSetBridge
open ExactGrothendieckGroup FDRepSimpleClassKZero IntegralBasicSetBridge
open OrdinaryIrreducibleCharacter ConlonBasicSet OddConformalProposition311Relative
open TypeBCliffordCarriers TypeBRationalSeriesBasicSet TypeBRationalSeriesSource
open TypeBSpinConlonBlockSourceInstantiation TypeBOddPrimesProposition44Relative
open TypeBSpecialCliffordActionAdapter TypeBIntegralSeriesSplitting

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- The global basic set is derived from consistent individual FLZ
packets, with the same algebraic Spin centre coinvariant order two. -/
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

/-- Naturality on the two factors composes to naturality on a product.
This is an elementary representation calculation without character data. -/
theorem natural_of_product_factors {D E : Type*} {X Y : Type*} [Monoid D] [Monoid E]
    [AddCommGroup X] [AddCommGroup Y]
    (red : X →+ Y) (ordinary : Representation ℤ (D × E) X)
    (modular : Representation ℤ (D × E) Y)
    (diagonal : ∀ d x, red (ordinary (d, 1) x) = modular (d, 1) (red x))
    (field : ∀ e x, red (ordinary (1, e) x) = modular (1, e) (red x)) :
    ∀ a x, red (ordinary a x) = modular a (red x) := by
  rintro ⟨d, e⟩ x
  have pair : (d, e) = (d, 1) * (1, e) := by simp
  rw [pair, map_mul, map_mul]
  change red (ordinary (d, 1) (ordinary (1, e) x)) =
    modular (d, 1) (modular (1, e) (red x))
  rw [diagonal, field]

section EffectiveActions

variable {parameters : OddFieldParameters F p f}
  (fieldSource : FieldActionSource n F p f parameters N)
  (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  (series : Irr K (Spin n F N) → Prop)
  [MulAction (TypeBSpinStabilizer.OuterGroup f) (OrdinarySeriesCarrier series)]
  [MulAction (TypeBSpinStabilizer.OuterGroup f) (IBr iota)]
  [MulAction (TypeBSpinStabilizer.OuterGroup f) (SpinBlock (k := k) (N := N))]

 /-- Reduction commutes with the actual inverse regular conjugation. -/
theorem reductionNatural_diagonal
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
      (OrdinarySeriesCarrier series)
      (decompositionMapOfStableReduction Msys iota hcompat))
    (S : EffectiveActionSource fieldSource iota hinj series basicSet)
    (g : SpecialClifford n F) (x : FDRepKZero K (Spin n F N)) :
    decompositionMapOfStableReduction Msys iota hcompat
        (S.labelled.ordinaryAction (S.diagonal g, 1) x) =
      S.labelled.modularAction (S.diagonal g, 1)
        (decompositionMapOfStableReduction Msys iota hcompat x) := by
  calc
    _ = decompositionMapOfStableReduction Msys iota hcompat
        (twistKZero (k := K) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) x) :=
      congrArg (decompositionMapOfStableReduction Msys iota hcompat)
        (S.ordinary_diagonal g x)
    _ = twistKZero (k := k) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
        (decompositionMapOfStableReduction Msys iota hcompat x) :=
      decompositionMapOfStableReduction_twist Msys iota hcompat _ x
    _ = _ := (S.modular_diagonal g _).symm

/-- Reduction commutes with the actual inverse field automorphism. -/
theorem reductionNatural_field
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
      (OrdinarySeriesCarrier series)
      (decompositionMapOfStableReduction Msys iota hcompat))
    (S : EffectiveActionSource fieldSource iota hinj series basicSet)
    (e : FieldGroup f) (x : FDRepKZero K (Spin n F N)) :
    decompositionMapOfStableReduction Msys iota hcompat
        (S.labelled.ordinaryAction (1, e) x) =
      S.labelled.modularAction (1, e)
        (decompositionMapOfStableReduction Msys iota hcompat x) := by
  calc
    _ = decompositionMapOfStableReduction Msys iota hcompat
        (twistKZero (k := K) (spinFieldAction n F fieldSource e⁻¹) x) :=
      congrArg (decompositionMapOfStableReduction Msys iota hcompat)
        (S.ordinary_field e x)
    _ = twistKZero (k := k) (spinFieldAction n F fieldSource e⁻¹)
        (decompositionMapOfStableReduction Msys iota hcompat x) :=
      decompositionMapOfStableReduction_twist Msys iota hcompat _ x
    _ = _ := (S.modular_field e _).symm

/-- The two actual factors give reduction naturality without ordinary
algebraic closure. The proof uses only the checked factor lemmas. -/
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
  change ∀ a x, decompositionMapOfStableReduction Msys iota hcompat
      (S.labelled.ordinaryAction a x) =
    S.labelled.modularAction a (decompositionMapOfStableReduction Msys iota hcompat x)
  apply natural_of_product_factors
    (decompositionMapOfStableReduction Msys iota hcompat)
    S.labelled.ordinaryAction S.labelled.modularAction
  · intro d x
    obtain ⟨g, hg⟩ := S.diagonal_surjective d
    subst d
    exact reductionNatural_diagonal fieldSource iota hinj series Msys hcompat basicSet S g x
  · exact reductionNatural_field fieldSource iota hinj series Msys hcompat basicSet S

end EffectiveActions

/-- The actual Spin block-lattice equivalence, two-hypoelementarity and
Conlon--Burnside equivariant bijection with consistent ordinary K.
Every literal source scope and carrier binding remains explicit. -/
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

end ModularRep.PaperProofs.TypeBSpinConlonSplittingSourceInstantiation



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
