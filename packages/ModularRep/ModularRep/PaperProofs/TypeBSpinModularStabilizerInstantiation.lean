import ModularRep.PaperProofs.TypeBSpinConlonModularInstantiation
import ModularRep.PaperProofs.TypeBSpinOrdinarySeparationBinding
import ModularRep.PaperProofs.OddConlonOrbitAssembly
import ModularRep.StabilizerFactorizationTransport

/-!
# Spin Brauer stabilizers from the actual modular Lemma 4.2 endpoint

Every representative matching below is obtained from the checked two-group
Lemma 4.2 application. Existing construction from orbit representatives constructs the global lower
matching. The exact FLZ ordinary separation on sufficient splitting
coefficients is then transferred through that same equivariant map.

The lower rational family is the actual regular restriction of the SAME
Jordan source. Its roots, specified blocks and effective diagonal/field
actions are the accepted constructed ones. No global lower matching,
Brauer separation, factorizing constituent or criterion conclusion is an
external source input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinModularStabilizerInstantiation

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

open TypeBSpinConlonModularInstantiation OddConlonOrbitAssembly
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

/-- Source-instantiated lower matching and effective Brauer stabilizer factorization. -/
theorem spin_brauer_stabilizers_modular_instantiated
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
        (A := MulAction.stabilizer (OuterGroup f) (orbitRepresentative orbit))),
    ∃ beta : IBr iota ≃ seriesSource.family.Basic,
      (∀ (a : OuterGroup f) (phi : IBr iota), beta (a • phi) = a • beta phi) ∧
      (∀ phi, ordinaryBlock Msys iota hinj seriesSource blocks ordinary (beta phi) =
        irreducibleBrauerCharacterBlock iota hinj blocks phi) ∧
      (∀ (phi : IBr iota) (g : SpecialClifford n F) (e : FieldGroup f),
        ((D.diagonal g, 1) : OuterGroup f) • (((1, e) : OuterGroup f) • phi) = phi ↔
          ((D.diagonal g, 1) : OuterGroup f) • phi = phi ∧
            ((1, e) : OuterGroup f) • phi = phi) := by
  dsimp only
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
  intro conlon burnside
  let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
  let blockOf := ordinaryBlock Msys iota hinj seriesSource blocks ordinary
  have hBrBlock : ∀ (a : OuterGroup f) (phi : IBr iota),
      brauerBlock (a • phi) = a • brauerBlock phi :=
    brauerBlock_action N D fs iota hinj blocks
  have hOrdBlock : ∀ (a : OuterGroup f) (x : seriesSource.family.Basic),
      blockOf (a • x) = a • blockOf x :=
    fun a x => ordinaryBlock_action N D fs Msys iota hcompat hinj blocks ordinary a x.val
  have representativeMaps : RepresentativeEquivExists brauerBlock blockOf hBrBlock := by
    intro orbit
    let b : SpinBlock (k := k) (N := N) := orbitRepresentative orbit
    let H := MulAction.stabilizer (OuterGroup f) b
    letI : MulAction H (BlockFibre blockOf b) := stabilizerFibreAction blockOf hOrdBlock b
    letI : MulAction H (BlockFibre brauerBlock b) := stabilizerFibreAction brauerBlock hBrBlock b
    have accepted := lemma_4_3_spin_modular_instantiated J fs centre Msys hcompat
      separation blocks ordinary unionSource existsAbove certificate fieldNatural b
      (conlon orbit) (burnside orbit)
    obtain ⟨localMap, localEquivariant⟩ := accepted.2.2
    refine ⟨localMap, ?_⟩
    intro a hfix phi
    exact congrArg Subtype.val (localEquivariant (⟨a, hfix⟩ : H) phi)
  let family := RepresentativeEquivFamily.ofExists brauerBlock blockOf hBrBlock representativeMaps
  let beta := RepresentativeEquivFamily.globalEquiv brauerBlock blockOf hBrBlock hOrdBlock family
  have hbeta : ∀ (a : OuterGroup f) (phi : IBr iota), beta (a • phi) = a • beta phi :=
    RepresentativeEquivFamily.globalEquiv_equivariant brauerBlock blockOf hBrBlock hOrdBlock family
  refine ⟨beta, hbeta,
    RepresentativeEquivFamily.globalEquiv_block_preserving brauerBlock blockOf hBrBlock hOrdBlock family,
    ?_⟩
  let diagonalHom : SpecialClifford n F →* OuterGroup f :=
    (MonoidHom.inl DiagonalGroup (FieldGroup f)).comp D.diagonal
  let fieldHom : FieldGroup f →* OuterGroup f :=
    MonoidHom.inr DiagonalGroup (FieldGroup f)
  letI : MulAction (SpecialClifford n F) (IBr iota) :=
    MulAction.compHom (IBr iota) diagonalHom
  letI : MulAction (FieldGroup f) (IBr iota) :=
    MulAction.compHom (IBr iota) fieldHom
  letI : MulAction (SpecialClifford n F) seriesSource.family.Basic :=
    MulAction.compHom seriesSource.family.Basic diagonalHom
  letI : MulAction (FieldGroup f) seriesSource.family.Basic :=
    MulAction.compHom seriesSource.family.Basic fieldHom
  intro phi g e
  have hOrdinary : ProductStabilizerFactorization
      (D := SpecialClifford n F) (E := FieldGroup f) (beta phi) := by
    intro d sigma
    exact TypeBSpinOrdinarySeparationBinding.selected_product_factorization
      parameters scope N fs centre ordinary310 seriesSource.family.selectedSeries
      diagonalStable fieldStable (beta phi) d sigma
  exact (brauerFactorization_of_ordinaryFactorization beta
    (fun d x => hbeta (diagonalHom d) x)
    (fun sigma x => hbeta (fieldHom sigma) x) phi hOrdinary) g e

end ModularRep.PaperProofs.TypeBSpinModularStabilizerInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
