import ModularRep.PaperProofs.TypeBSpinConlonModularInstantiation

/-!
# The particular Spin block decomposition map in `lem:type-b-conlon-block`

The September 8 manuscript, lines 106--122 and 149--150, asserts that the
particular decomposition map restricts to an equivariant integral lattice
isomorphism. The accepted Spin endpoint already constructs that map but
retains only existence of a lattice equivalence in its public result.
This module exposes the SAME chosen individual FLZ Theorem 2.3 packet's
specified block restriction, its full exact K0 equation and its generator
equation. It constructs the lattice intertwining from the separate actual
diagonal and field actions and checked stable-reduction naturality.

Minimal external data are the literal Spin norm kernel and diagonal quotient,
field automorphisms, the source-indexed individual rational-series FLZ2.3
certificate at algebraic centre coinvariant order TWO, the SAME modular
system/root and specified ordinary block source, and separate series stability
under the two twists. FLZ Theorem 2.3 p.537 is E2; same-root stable reduction
and specified block support are E1 (Navarro 2.9 p.23, 3.3/3.11/3.13(b));
actual finite-point/centre identifications are the existing E1 source facts.
A source-instantiated application must use the designated SAME Jordan family,
its literal lower restriction and the existing constructed norm diagonal map.

No global basic set, blockwise lattice equivalence, naturality, faithful action
or desired bijection is an external input. The final joint manuscript endpoint
reuses the accepted Conlon--Burnside deduction and identifies the actual outer
quotient; this module does not assert that identification on its own.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBOddPrimeSpinDecomposition

open ModularRep BlockFibreRestriction DecompositionBasicSetBridge
open ExactGrothendieckGroup FDRepSimpleClassKZero IntegralBasicSetBridge
open OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesSplitting
open TypeBSpecialCliffordActionAdapter
open OddConformalProposition311Relative TypeBOddPrimesProposition44Relative
section Spin

open TypeBSpinStabilizer TypeBSpinDiagonalFieldQuotient
open TypeBSpinConlonBlockSourceInstantiation TypeBSpinConlonPhysicalSourceInstantiation
open TypeBSpinConlonSplittingSourceInstantiation TypeBSpinEffectiveSourceBinding

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} [Finite (Spin n F N)]
  [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- The literal specified Spin block restriction of the SAME chosen
individual FLZ Theorem 2.3 packet. This definition supplies a stable name
for the particular decomposition map transported by the quotient endpoint. -/
def spinBlockBasicSet
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks)
    (certificate : Theorem23Certificate Msys iota hcompat hinj source.family
      blocks source.blockSeries p 2)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    (b : SpinBlock (k := k) (N := N)) :=
  let blockOf := ordinaryBlock Msys iota hinj source blocks ordinary
  let basic := spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
    certificate hEll hOdd hNondef
  let hd := blockDiagonalLinearEquiv_of_generator_support blockOf
    (irreducibleBrauerCharacterBlock iota hinj blocks) basic.linearEquiv
    (forwardGenerator Msys iota hcompat hinj source blocks ordinary certificate hEll hOdd hNondef)
  restrictRestrictedIntegralBasicSet basic.toRestrictedIntegralBasicSet
    blockOf (irreducibleBrauerCharacterBlock iota hinj blocks) hd b

/-- The actual Spin decomposition lattice retains the same individual
Theorem 2.3 packet and specified block restriction as the accepted endpoint.
The separate diagonal and field stability inputs construct its natural
class actions; no faithful-action hypothesis is used. -/
theorem spin_decomposition_lattice
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    {parameters : OddFieldParameters F p f}
    (fs : FieldActionSource n F p f parameters N) (D : DiagonalSource N)
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks)
    (certificate : Theorem23Certificate Msys iota hcompat hinj source.family
      blocks source.blockSeries p 2)
    (diagonalStable : ∀ (g : SpecialClifford n F) (chi : Irr K (Spin n F N)),
      source.family.selectedSeries chi → source.family.selectedSeries
        (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
          (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)))
    (fieldStable : ∀ (e : FieldGroup f) (chi : Irr K (Spin n F N)),
      source.family.selectedSeries chi → source.family.selectedSeries
        (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
          (spinFieldAction n F fs e⁻¹)))
    (b : SpinBlock (k := k) (N := N)) :
    let _ := selectedSeriesAction N D fs source.family.selectedSeries diagonalStable fieldStable
    let _ := brauerAction N D fs iota
    let _ := blockAction (k := k) N D fs
    let hOrd : ∀ (a : OuterGroup f) (x : source.family.Basic),
        ordinaryBlock Msys iota hinj source blocks ordinary (a • x) =
          a • ordinaryBlock Msys iota hinj source blocks ordinary x :=
      fun a x => ordinaryBlock_action N D fs Msys iota hcompat hinj blocks ordinary a x.val
    let hBr := brauerBlock_action N D fs iota hinj blocks
    let J := MulAction.stabilizer (OuterGroup f) b
    let blockOf := ordinaryBlock Msys iota hinj source blocks ordinary
    let _ : MulAction J (BlockFibre blockOf b) := stabilizerFibreAction blockOf hOrd b
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks) hBr b
    let restricted := spinBlockBasicSet Msys iota hcompat hinj source blocks
      ordinary certificate hEll hOdd hNondef b
    ∃ dB : (Representation.ofMulAction ℤ J (BlockFibre blockOf b)).Equiv
        (Representation.ofMulAction ℤ J
          (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b)),
      dB.toLinearEquiv = restricted.linearEquiv ∧
      (∀ v, labelledSimpleClassKZero restricted.modularLabel (dB.toLinearEquiv v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero restricted.ordinaryLabel v)) ∧
      (∀ x : BlockFibre blockOf b,
        labelledSimpleClassKZero restricted.modularLabel
          (dB.toLinearEquiv (MonoidAlgebra.single x 1)) =
        decompositionMapOfStableReduction Msys iota hcompat
          (simpleClassToFDRepKZeroGenerator (restricted.ordinaryLabel x))) := by
  classical
  dsimp only
  letI := selectedSeriesAction N D fs source.family.selectedSeries diagonalStable fieldStable
  letI := brauerAction N D fs iota
  letI := blockAction (k := k) N D fs
  let hOrd : ∀ (a : OuterGroup f) (x : source.family.Basic),
      ordinaryBlock Msys iota hinj source blocks ordinary (a • x) =
        a • ordinaryBlock Msys iota hinj source blocks ordinary x :=
    fun a x => ordinaryBlock_action N D fs Msys iota hcompat hinj blocks ordinary a x.val
  let hBr := brauerBlock_action N D fs iota hinj blocks
  let J := MulAction.stabilizer (OuterGroup f) b
  let blockOf := ordinaryBlock Msys iota hinj source blocks ordinary
  letI : MulAction J (BlockFibre blockOf b) := stabilizerFibreAction blockOf hOrd b
  letI : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
    stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks) hBr b
  let basic := spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
    certificate hEll hOdd hNondef
  let hd := blockDiagonalLinearEquiv_of_generator_support blockOf
    (irreducibleBrauerCharacterBlock iota hinj blocks) basic.linearEquiv
    (forwardGenerator Msys iota hcompat hinj source blocks ordinary certificate hEll hOdd hNondef)
  let ambient := effectiveActionSource N D fs Msys iota hcompat hinj blocks source certificate
    hEll hOdd hNondef diagonalStable fieldStable
  have ambientNatural := reductionNatural_of_effectiveActionSource fs iota hinj
    source.family.selectedSeries Msys hcompat basic ambient
  let actions := restrictLabelledKZeroActionDataToSubgroup basic ambient.labelled J
    (fun _ _ => rfl) (fun _ _ => rfl)
  have natural := decompositionNatural_restrict_subgroup basic ambient.labelled ambientNatural
    J (fun _ _ => rfl) (fun _ _ => rfl)
  let restricted := spinBlockBasicSet Msys iota hcompat hinj source blocks
    ordinary certificate hEll hOdd hNondef b
  have matrix : MatrixEquivariant (A := J) restricted.linearEquiv.toLinearMap :=
    matrixEquivariant_restrictBlock_of_kZero_naturality basic.toRestrictedIntegralBasicSet
      hd actions natural (fun _ _ => rfl) (fun _ _ => rfl)
  let dB := permutationLatticeEquiv restricted.linearEquiv matrix
  refine ⟨dB, rfl, ?_, ?_⟩
  · exact restricted.restricts_decomposition
  · intro x
    change labelledSimpleClassKZero restricted.modularLabel
        (restricted.linearEquiv (MonoidAlgebra.single x 1)) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator (restricted.ordinaryLabel x))
    simpa only [labelledSimpleClassKZero_single] using
      restricted.restricts_decomposition (MonoidAlgebra.single x 1)

end Spin

section ModularSource

open ConlonBasicSet
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

/-- On the SAME published Jordan family, actual modular-system root and norm
diagonal quotient, the particular Spin decomposition map is an integral
permutation-lattice isomorphism and the accepted Conlon deduction provides
the actual blockwise equivariant bijection. No target conclusion is an input. -/
theorem spin_modular_conlon_decomposition
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
    let diagonalStable := selected_diagonal_stable (fullFamily N J separation)
      (rationalSeries_diagonal N J)
    let fieldStable := selected_field_stable parameters fs (fullFamily N J separation)
      (rationalSeries_field N J fs fieldNatural)
    let D := diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
    let _ := selectedSeriesAction N D fs rational.family.selectedSeries diagonalStable fieldStable
    let _ := brauerAction N D fs iota
    let _ := blockAction (k := k) N D fs
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
    IsPHypoelementary 2 stabilizer ∧
      (∃ dB : (Representation.ofMulAction ℤ stabilizer (BlockFibre blockOf b)).Equiv
          (Representation.ofMulAction ℤ stabilizer
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
        ∀ (j : stabilizer) phi, e (j • phi) = j • e phi := by
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
  intro conlon burnside
  have accepted := TypeBSpinConlonModularInstantiation.lemma_4_3_spin_modular_instantiated
    J fs centre Msys hcompat separation blocks ordinary unionSource existsAbove certificate
    fieldNatural b conlon burnside
  let source23 := theorem23Certificate (fullFamily N J separation)
    parameters.prime scope.modular_prime scope.nondefining Msys iota hinj blocks ordinary
    unionSource hcompat existsAbove certificate
  have named := spin_decomposition_lattice scope.modular_prime scope.modular_odd scope.nondefining
    fs D Msys iota hcompat hinj rational blocks ordinary source23 diagonalStable fieldStable b
  exact ⟨accepted.1, named, accepted.2.2⟩

end ModularSource
end ModularRep.PaperProofs.TypeBOddPrimeSpinDecomposition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
