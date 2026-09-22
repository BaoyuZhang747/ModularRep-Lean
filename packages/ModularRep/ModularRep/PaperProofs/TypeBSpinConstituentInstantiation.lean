import ModularRep.PaperProofs.TypeBSpinModularStabilizerInstantiation
import ModularRep.PaperProofs.TypeBSpinAmbientFactorizationBinding
import ModularRep.PaperProofs.TypeBSpinRestrictionConstituent

/-!
# A literal restriction constituent with constructed ambient inertia

Both character roots come from the same modular system and ordinary
cyclotomic choice. The lower root is definitionally the restriction of the
upper root. The existing positive restriction expansion, Navarro (2.2)(d)
and (2.3), pp. 18--19, supplies a nonzero coefficient on these functions.

The lower matching and its effective Brauer stabilizer factorization are
derived by the modular Spin theorem. The actual ambient conversion then
applies to the chosen constituent. No constituent, matching, or inertia
factorization is part of the positive expansion input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBSpinConstituentInstantiation

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
open TypeBSpinModularStabilizerInstantiation TypeBSpinAmbientFactorizationBinding
open TypeBWeightStabilizerSource NavarroCoveringBrauerExtension
open OddConlonOrbitAssembly

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F}
  {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
  {primary : TypeBFLZPrimarySource.PrimarySource parameters scope}
  {source : OccurringCharacterSource (K := K) parameters scope primary}
  {choice : Choice (F := F) (n := n) K} {values : JordanValues source}

/-- A nonzero coefficient of the same positive expansion selects an actual
constituent, with no additional requirement on the ordinary value field. -/
theorem exists_spin_constituent_of_positive_expansion
    (N : NormSource n F)
    (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (restriction : TypeBSpinRestrictionConstituent.RestrictionExpansionSource N iotaA)
    (Phi : IBr iotaA) :
    ∃ phi : IBr (TypeBSpinRestrictionConstituent.spinRoot N iotaA),
      BrauerOccursInRestriction (SpinSubgroup n F N) iotaA
        (TypeBSpinRestrictionConstituent.spinRoot N iotaA) Phi phi := by
  classical
  have hexists : ∃ phi, restriction.multiplicity Phi phi ≠ 0 := by
    by_contra h
    apply restriction.nonzero Phi
    ext phi
    exact not_not.mp (fun hphi => h ⟨phi, hphi⟩)
  obtain ⟨phi, hphi⟩ := hexists
  exact ⟨phi, restriction.multiplicity Phi, hphi, restriction.value Phi⟩

/-- Every actual upper Brauer character has a literal lower constituent
whose ambient inertia is the product of its two actual inertia images. -/
theorem exists_spin_constituent_with_ambient_factorization_modular_instantiated
    (J : JordanCertificate source choice values)
    (fs : FieldActionSource n F p f parameters N)
    (centre : CentreSource n F parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank))
    (Msys : ModularSystem ell K O k) :
    let iotaA := TypeBFLZModularRootBinding.cliffordRoot Msys choice
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
    (ordinary310 : TypeBSpinOrdinarySeparationBinding.Theorem310Source parameters scope N fs (K := K)),
    let seriesSource := rationalSource (fullFamily N J separation) parameters.prime scope.modular_prime scope.nondefining
      Msys iota hinj blocks ordinary unionSource
    let diagonalStable := selected_diagonal_stable (ell := ell) (fullFamily N J separation)
      (rationalSeries_diagonal N J)
    let fieldStable := selected_field_stable (ell := ell) parameters fs (fullFamily N J separation)
      (rationalSeries_field N J fs fieldNatural)
    let D := diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
    let _ := selectedSeriesAction N D fs seriesSource.family.selectedSeries diagonalStable fieldStable
    let _ := brauerAction N D fs iota
    let _ := blockAction (k := k) N D fs
    ∀ (conlon : ∀ orbit : BlockOrbit (OuterGroup f) (SpinBlock (k := k) (N := N)),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (OuterGroup f) (orbitRepresentative orbit)))
      (burnside : ∀ orbit : BlockOrbit (OuterGroup f) (SpinBlock (k := k) (N := N)),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (OuterGroup f) (orbitRepresentative orbit)))
      (restriction : TypeBSpinRestrictionConstituent.RestrictionExpansionSource N iotaA)
      (Phi : IBr iotaA),
    ∃ phi : IBr iota,
      BrauerOccursInRestriction (SpinSubgroup n F N) iotaA iota Phi phi ∧
      (ambientBrauerInertia N fs iota phi : Set (Ambient fs)) =
        (specialCliffordInertiaImage N fs iota phi : Set (Ambient fs)) *
          (fieldInertiaImage N fs iota phi : Set (Ambient fs)) := by
  dsimp only
  let iotaA := TypeBFLZModularRootBinding.cliffordRoot Msys choice
  let iota := TypeBFLZModularRootBinding.spinRoot Msys choice N
  let hinj : IrreducibleBrauerCharacterInjectivity iota :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  intro hcompat
  letI := choice.ordinaryRoots
  letI := spinRoots N choice
  intro separation finiteOrdinary finiteBlocks blocks ordinary unionSource existsAbove certificate
    fieldNatural ordinary310
  let seriesSource := rationalSource (fullFamily N J separation) parameters.prime
    scope.modular_prime scope.nondefining Msys iota hinj blocks ordinary unionSource
  let diagonalStable := selected_diagonal_stable (ell := ell) (fullFamily N J separation)
    (rationalSeries_diagonal N J)
  let fieldStable := selected_field_stable (ell := ell) parameters fs (fullFamily N J separation)
    (rationalSeries_field N J fs fieldNatural)
  let D := diagonalSource n F N parameters
    (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
  letI := selectedSeriesAction N D fs seriesSource.family.selectedSeries diagonalStable fieldStable
  letI := brauerAction N D fs iota
  letI := blockAction (k := k) N D fs
  intro conlon burnside restriction Phi
  obtain ⟨beta, hbeta, hblock, factorization⟩ :=
    spin_brauer_stabilizers_modular_instantiated J fs centre Msys hcompat
      separation blocks ordinary unionSource existsAbove certificate fieldNatural ordinary310
      conlon burnside
  obtain ⟨phi, hphi⟩ := exists_spin_constituent_of_positive_expansion N iotaA restriction Phi
  refine ⟨phi, hphi, ?_⟩
  exact ambient_inertia_product_of_effective N D fs iota phi (factorization phi)

end ModularRep.PaperProofs.TypeBSpinConstituentInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
