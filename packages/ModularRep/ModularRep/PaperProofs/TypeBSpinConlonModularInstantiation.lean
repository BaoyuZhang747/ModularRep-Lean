import ModularRep.PaperProofs.TypeBSpinConlonRegularRestrictionInstantiation
import ModularRep.PaperProofs.TypeBFLZModularRootBinding
import ModularRep.BrauerCharacterSeparation

/-!
# The same-source Spin Conlon endpoint with the actual modular root

Use the literal restriction of the SC modular-system root and the checked
Brauer separation theorem. The lower rational family, diagonal/field/block
actions, exact decomposition map and stabilizer remain precisely those of
the existing regular-restriction consumer. No independent root, injectivity,
lower rational family or blockwise target is an input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinConlonModularInstantiation

open ModularRep BlockFibreRestriction FDRepSimpleClassKZero IntegralBasicSetBridge
open OrdinaryIrreducibleCharacter ConlonBasicSet
open TypeBCliffordCarriers TypeBSpinStabilizer TypeBSpinDiagonalFieldQuotient
open TypeBSpinConlonBlockSourceInstantiation TypeBSpinConlonPhysicalSourceInstantiation
open TypeBSpinEffectiveSourceBinding TypeBIntegralSeriesSplitting
open TypeBCliffordCentreSource TypeBSpinDiagonalNormSource
open TypeBSpinConlonNormSourceInstantiation TypeBSpinBroueMichelSourceBinding
open TypeBSpinBroueMichelCarriers TypeBSpinRationalIndexAction TypeBRationalSeriesSource
open TypeBFLZLabelSource TypeBFLZOccurringCharacterSource
open TypeBFLZJordanSourceBinding TypeBFLZCyclotomicModel
open TypeBConformalRationalProjection TypeBSpinJordanRestrictionSource
open TypeBSpinConlonBroueMichelInstantiation

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F}
  {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
  {primary : TypeBFLZPrimarySource.PrimarySource parameters scope}
  {source : OccurringCharacterSource (K := K) parameters scope primary}
  {choice : Choice (F := F) (n := n) K} {values : JordanValues source}

/-- The full actual Spin block conclusion with root and Brauer separation
constructed from the SAME modular system and ordinary cyclotomic choice. -/
theorem lemma_4_3_spin_modular_instantiated
    (J : JordanCertificate source choice values)
    (fs : FieldActionSource n F p f parameters N)
    (centre : CentreSource n F parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank))
    (Msys : ModularSystem ell K O k) :
    let iota := TypeBFLZModularRootBinding.spinRoot Msys choice N
    let hinj : IrreducibleBrauerCharacterInjectivity iota :=
      irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    ∀ (hcompat : StableReductionBrauerCharacterCompatibility Msys iota),
    letI := choice.ordinaryRoots
    letI := spinRoots N choice
    ∀ (separation : SeparationCertificate N J)
    [Finite (selectedFamily (ell := ell) (fullFamily N J separation)).Basic]
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks)
    (unionSource : BlockUnionCertificate (fullFamily N J separation) parameters.prime scope.modular_prime scope.nondefining
      Msys iota hinj blocks ordinary)
    (existsAbove : ∀ phi : IBr iota, ∃ chi : Irr K (Spin n F N),
      TypeBOrdinaryBlockSplitting.decompositionNumber Msys iota chi phi ≠ 0)
    (certificate : LiteralTheorem23Certificate (fullFamily N J separation) parameters.prime scope.modular_prime scope.nondefining
      Msys iota hinj hcompat)
    (fieldNatural : ∀ (e : FieldGroup f) (s : SemisimpleParameter F p n)
      (Phi : Irr K (SpecialClifford n F)), J.rationalSeries s Phi →
        J.rationalSeries (semisimpleField parameters e s)
          (OrdinaryIrreducibleCharacter.twist K (SpecialClifford n F) Phi (fs.action e⁻¹)))
    (b : SpinBlock (k := k) (N := N)),
    let source := rationalSource (fullFamily N J separation) parameters.prime scope.modular_prime scope.nondefining
      Msys iota hinj blocks ordinary unionSource
    let diagonalStable := selected_diagonal_stable (fullFamily N J separation)
      (rationalSeries_diagonal N J)
    let fieldStable := selected_field_stable parameters fs (fullFamily N J separation)
      (rationalSeries_field N J fs fieldNatural)
    let D := diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
    let _ := selectedSeriesAction N D fs source.family.selectedSeries diagonalStable fieldStable
    let _ := brauerAction N D fs iota
    let _ := blockAction (k := k) N D fs
    ∀ (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (OuterGroup f) b))
      (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (OuterGroup f) b)),
    let hOrdinary : ∀ (a : OuterGroup f) (x : source.family.Basic),
        ordinaryBlock Msys iota hinj source blocks ordinary (a • x) =
          a • ordinaryBlock Msys iota hinj source blocks ordinary x :=
      fun a x => ordinaryBlock_action N D fs Msys iota hcompat hinj blocks ordinary a x.val
    let hBrauer : ∀ (a : OuterGroup f) (phi : IBr iota),
        irreducibleBrauerCharacterBlock iota hinj blocks (a • phi) =
          a • irreducibleBrauerCharacterBlock iota hinj blocks phi :=
      brauerBlock_action N D fs iota hinj blocks
    let J := MulAction.stabilizer (OuterGroup f) b
    let blockOf := ordinaryBlock Msys iota hinj source blocks ordinary
    let _ : MulAction J (BlockFibre blockOf b) :=
      stabilizerFibreAction blockOf hOrdinary b
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks) hBrauer b
    IsPHypoelementary 2 J ∧
      Nonempty ((Representation.ofMulAction ℤ J (BlockFibre blockOf b)).Equiv
        (Representation.ofMulAction ℤ J
          (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
          BlockFibre blockOf b,
        ∀ (j : J) (phi : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b),
          e (j • phi) = j • e phi :=
  let iota := TypeBFLZModularRootBinding.spinRoot Msys choice N
  let hinj : IrreducibleBrauerCharacterInjectivity iota :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  fun hcompat =>
    TypeBSpinConlonRegularRestrictionInstantiation.lemma_4_3_spin_regular_restriction_instantiated
      J fs centre Msys iota hcompat hinj

end ModularRep.PaperProofs.TypeBSpinConlonModularInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
