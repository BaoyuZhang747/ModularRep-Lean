import ModularRep.PaperProofs.TypeBOddPrimeSpinOuterQuotient
import ModularRep.PaperProofs.TypeBOddPrimeSpinDecomposition

/-!
# The revised Type B Conlon deduction on the literal natural quotient

The manuscript endpoint is `lem:type-b-conlon-block`, September 8 source
57FA7764 with the separately recorded centre-notation clarification 2CD7F193.
The Spin actor is Aut(Spin)_B / Inn(Spin). We retain the actual ordinary and
Brauer block fibres, the same restricted decomposition map and the Conlon
bijection already constructed from the source-instantiated integral packet.
The only additional structural input is the literal outer-coordinate theorem
of FLZ Section 3.5 with its diagonal and field generator equations. Natural
quotient actions are proved to agree independently on characters and blocks;
no action is assumed faithful. The preliminary actor-restriction helper is
supporting machinery, not an independently accepted manuscript window.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBOddPrimeConlonWindow

open ModularRep IntegralBasicSetBridge

/-- Changing the actor along a homomorphism retains the very same linear map. -/
def restrictLatticeActor {A J X Y : Type} [Group A] [Group J]
    [MulAction A X] [MulAction A Y] (h : J →* A)
    (d : (Representation.ofMulAction ℤ A X).Equiv
      (Representation.ofMulAction ℤ A Y)) :
    letI := MulAction.compHom X h
    letI := MulAction.compHom Y h
    (Representation.ofMulAction ℤ J X).Equiv
      (Representation.ofMulAction ℤ J Y) :=
  Representation.Equiv.mk d.toLinearEquiv
    (fun j => d.toIntertwiningMap.isIntertwining' (h j))

open BlockFibreRestriction DecompositionBasicSetBridge
open ExactGrothendieckGroup FDRepSimpleClassKZero OrdinaryIrreducibleCharacter ConlonBasicSet
open TypeBCliffordCarriers TypeBOddPrimeSpinDecomposition

open TypeBSpinStabilizer TypeBSpinDiagonalFieldQuotient
open TypeBSpinConlonBlockSourceInstantiation TypeBSpinConlonPhysicalSourceInstantiation
open TypeBSpinConlonSplittingSourceInstantiation TypeBSpinEffectiveSourceBinding
open TypeBCliffordCentreSource TypeBSpinDiagonalNormSource
open TypeBSpinBroueMichelSourceBinding TypeBSpinBroueMichelCarriers
open TypeBSpinRationalIndexAction TypeBRationalSeriesSource
open TypeBFLZLabelSource TypeBFLZOccurringCharacterSource
open TypeBFLZJordanSourceBinding TypeBFLZCyclotomicModel
open TypeBConformalRationalProjection TypeBSpinJordanRestrictionSource

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F}
  {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
  {primary : TypeBFLZPrimarySource.PrimarySource parameters scope}
  {source : OccurringCharacterSource (K := K) parameters scope primary}
  {choice : Choice (F := F) (n := n) K} {values : JordanValues source}


/-- The revised manuscript Spin conclusion, on the actual natural outer block quotient. -/
theorem spin_revised_conlon_block
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
    (unionSource : BlockUnionCertificate (fullFamily N J separation)
      parameters.prime scope.modular_prime scope.nondefining Msys iota hinj blocks ordinary)
    (existsAbove : ∀ phi : IBr iota, ∃ chi : Irr K (Spin n F N),
      TypeBOrdinaryBlockSplitting.decompositionNumber Msys iota chi phi ≠ 0)
    (certificate : LiteralTheorem23Certificate (fullFamily N J separation)
      parameters.prime scope.modular_prime scope.nondefining Msys iota hinj hcompat)
    (fieldNatural : ∀ (e : FieldGroup f) (s : SemisimpleParameter F p n)
      (Phi : Irr K (SpecialClifford n F)), J.rationalSeries s Phi →
        J.rationalSeries (semisimpleField parameters e s)
          (OrdinaryIrreducibleCharacter.twist K (SpecialClifford n F) Phi (fs.action e⁻¹)))
    (b : SpinBlock (k := k) (N := N)),
    let rational := rationalSource (fullFamily N J separation)
      parameters.prime scope.modular_prime scope.nondefining Msys iota hinj blocks ordinary unionSource
    let diagonalStable := selected_diagonal_stable (ell := ell) (fullFamily N J separation)
      (rationalSeries_diagonal N J)
    let fieldStable := selected_field_stable (ell := ell) parameters fs (fullFamily N J separation)
      (rationalSeries_field N J fs fieldNatural)
    let D := diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
    let _ := selectedSeriesAction N D fs rational.family.selectedSeries diagonalStable fieldStable
    let _ := brauerAction N D fs iota
    let _ := blockAction (k := k) N D fs
    ∀ (coordinates : TypeBOddPrimeSpinOuterQuotient.OuterCoordinates N D fs scope.rank),
    ∀ (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (OuterGroup f) b))
      (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (OuterGroup f) b)),
    let hOrd : ∀ (a : OuterGroup f) (x : rational.family.Basic),
        ordinaryBlock Msys iota hinj rational blocks ordinary (a • x) =
          a • ordinaryBlock Msys iota hinj rational blocks ordinary x :=
      fun a x => ordinaryBlock_action N D fs Msys iota hcompat hinj blocks ordinary a x.val
    let hBr := brauerBlock_action N D fs iota hinj blocks
    let source23 := theorem23Certificate (fullFamily N J separation)
      parameters.prime scope.modular_prime scope.nondefining Msys iota hinj blocks ordinary
      unionSource hcompat existsAbove certificate
    let restricted := spinBlockBasicSet Msys iota hcompat hinj rational blocks ordinary
      source23 scope.modular_prime scope.modular_odd scope.nondefining b
    let stabilizer := MulAction.stabilizer (OuterGroup f) b
    let blockOf := ordinaryBlock Msys iota hinj rational blocks ordinary
    let _ : MulAction stabilizer (BlockFibre blockOf b) := stabilizerFibreAction blockOf hOrd b
    let _ : MulAction stabilizer
        (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks) hBr b
    let quotient := TypeBOddPrimeSpinOuterQuotient.BlockQuotient N b
    let transport : quotient →* stabilizer :=
      (TypeBOddPrimeSpinOuterQuotient.blockQuotientEquiv N D fs coordinates b).toMonoidHom
    let _ : MulAction quotient (BlockFibre blockOf b) := MulAction.compHom _ transport
    let _ : MulAction quotient
        (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      MulAction.compHom _ transport
    IsPHypoelementary 2 quotient ∧
      (∀ (j : quotient) (x : BlockFibre blockOf b),
        (j • x).val.val = TypeBOddPrimeSpinOuterQuotient.outerOrdinaryHom (K := K) N
          (TypeBOddPrimeSpinOuterQuotient.blockQuotientToOuter N b j) x.val.val) ∧
      (∀ (j : quotient)
        (phi : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b),
        (j • phi).val = TypeBOddPrimeSpinOuterQuotient.outerBrauerHom N iota
          (TypeBOddPrimeSpinOuterQuotient.blockQuotientToOuter N b j) phi.val) ∧
      (∃ dB : (Representation.ofMulAction ℤ quotient (BlockFibre blockOf b)).Equiv
          (Representation.ofMulAction ℤ quotient
            (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b)),
        dB.toLinearEquiv = restricted.linearEquiv ∧
        (∀ v, labelledSimpleClassKZero restricted.modularLabel (dB.toLinearEquiv v) =
          decompositionMapOfStableReduction Msys iota hcompat
            (labelledSimpleClassKZero restricted.ordinaryLabel v)) ∧
        (∀ x : BlockFibre blockOf b,
          labelledSimpleClassKZero restricted.modularLabel
            (dB.toLinearEquiv (MonoidAlgebra.single x 1)) =
          decompositionMapOfStableReduction Msys iota hcompat
            (simpleClassToFDRepKZeroGenerator (restricted.ordinaryLabel x)))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
          BlockFibre blockOf b,
        ∀ (j : quotient) phi, e (j • phi) = j • e phi := by
  classical
  dsimp only
  intro hcompat
  letI := choice.ordinaryRoots
  letI := spinRoots N choice
  intro separation finiteBasic finiteBlocks blocks ordinary unionSource existsAbove certificate fieldNatural b
  let iota := TypeBFLZModularRootBinding.spinRoot Msys choice N
  let hinj : IrreducibleBrauerCharacterInjectivity iota :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let rational := rationalSource (fullFamily N J separation)
    parameters.prime scope.modular_prime scope.nondefining Msys iota hinj blocks ordinary unionSource
  let diagonalStable := selected_diagonal_stable (ell := ell) (fullFamily N J separation)
    (rationalSeries_diagonal N J)
  let fieldStable := selected_field_stable (ell := ell) parameters fs (fullFamily N J separation)
    (rationalSeries_field N J fs fieldNatural)
  let D := diagonalSource n F N parameters
    (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
  letI := selectedSeriesAction N D fs rational.family.selectedSeries diagonalStable fieldStable
  letI := brauerAction N D fs iota
  letI := blockAction (k := k) N D fs
  intro coordinates conlon burnside
  let hOrd : ∀ (a : OuterGroup f) (x : rational.family.Basic),
      ordinaryBlock Msys iota hinj rational blocks ordinary (a • x) =
        a • ordinaryBlock Msys iota hinj rational blocks ordinary x :=
    fun a x => ordinaryBlock_action N D fs Msys iota hcompat hinj blocks ordinary a x.val
  let hBr := brauerBlock_action N D fs iota hinj blocks
  let stabilizer := MulAction.stabilizer (OuterGroup f) b
  let blockOf := ordinaryBlock Msys iota hinj rational blocks ordinary
  letI : MulAction stabilizer (BlockFibre blockOf b) := stabilizerFibreAction blockOf hOrd b
  letI : MulAction stabilizer
      (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
    stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks) hBr b
  have accepted := TypeBOddPrimeSpinDecomposition.spin_modular_conlon_decomposition
    J fs centre Msys hcompat separation blocks ordinary unionSource existsAbove certificate
    fieldNatural b conlon burnside
  rcases accepted with ⟨_, ⟨d, hd, hall, hgen⟩, e, he⟩
  let quotient := TypeBOddPrimeSpinOuterQuotient.BlockQuotient N b
  let transport : quotient →* stabilizer :=
    (TypeBOddPrimeSpinOuterQuotient.blockQuotientEquiv N D fs coordinates b).toMonoidHom
  letI : MulAction quotient (BlockFibre blockOf b) := MulAction.compHom _ transport
  letI : MulAction quotient
      (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
    MulAction.compHom _ transport
  refine ⟨TypeBOddPrimeSpinOuterQuotient.blockQuotient_twoHypoelementary N D fs coordinates b,
    ?_, ?_, ⟨restrictLatticeActor transport d, hd, hall, hgen⟩, e, ?_⟩
  · intro j x
    change TypeBSpinEffectiveClassActions.effectiveOrdinaryHom (k := K) N D fs
      (transport j).val x.val.val = _
    rw [TypeBOddPrimeSpinOuterQuotient.outerOrdinaryHom_coordinates N D fs coordinates,
      TypeBOddPrimeSpinOuterQuotient.blockQuotient_coordinates N D fs coordinates]
    rfl
  · intro j phi
    change TypeBSpinEffectiveClassActions.effectiveBrauerHom N D fs iota
      (transport j).val phi.val = _
    rw [TypeBOddPrimeSpinOuterQuotient.outerBrauerHom_coordinates N D fs coordinates,
      TypeBOddPrimeSpinOuterQuotient.blockQuotient_coordinates N D fs coordinates]
    rfl
  · intro j phi
    exact he (transport j) phi

end ModularRep.PaperProofs.TypeBOddPrimeConlonWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
