import ModularRep.PaperProofs.TypeBSpinConlonSplittingSourceInstantiation
import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting

/-!
# Spin Lemma 4.2 on the specified ordinary block selector

Restrict the actual ordinary block selector to the SAME Spin rational-series
carrier. Its forward support is the checked specified decomposition theorem
applied to exactly the FLZ Theorem 2.3 packet chosen by the frozen Spin basic
set. No independently chosen integral map or selected support premise occurs.

The resulting endpoint reuses the frozen Spin Conlon deduction. Literal
finite-point/rational-series/centre, modular roots and effective outer-action
source identifications remain explicit. This module adds no source record.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinConlonPhysicalSourceInstantiation

open ModularRep BlockFibreRestriction FDRepSimpleClassKZero IntegralBasicSetBridge
open OrdinaryIrreducibleCharacter ConlonBasicSet OddConformalProposition311Relative
open TypeBCliffordCarriers TypeBSpinConlonBlockSourceInstantiation
open TypeBSpinConlonSplittingSourceInstantiation TypeBIntegralSeriesSplitting

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} [Finite (Spin n F N)]
  [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- The selected ordinary character retains its actual specified block. -/
def ordinaryBlock
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks)
    (x : source.family.Basic) : SpinBlock (k := k) (N := N) :=
  ordinary.physical.ordinaryBlock x.val

/-- The exact chosen FLZ packet has specified forward block support. -/
theorem forwardGenerator
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
    (x : source.family.Basic) :
    (TypeBSpinConlonSplittingSourceInstantiation.spinBasicSetFromTheorem23
      Msys iota hcompat hinj source blocks
      certificate hEll hOdd hNondef).linearEquiv (MonoidAlgebra.single x 1) ∈
      MonoidAlgebra.supported ℤ ℤ
        (blockFibreSet (irreducibleBrauerCharacterBlock iota hinj blocks)
          (ordinaryBlock Msys iota hinj source blocks ordinary x)) := by
  unfold TypeBSpinConlonSplittingSourceInstantiation.spinBasicSetFromTheorem23 ordinaryBlock
  apply TypeBOrdinaryBlockSplitting.forwardSupport

/-- The actual Spin block-lattice equivalence, stabilizer and equivariant
bijection with its ordinary selector and support fixed by specified reduction.
The inherited rational-series and effective-action source boundaries remain. -/
theorem lemma_4_3_spin_physical_source_instantiated
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
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks)
    (certificate : Theorem23Certificate Msys iota hcompat hinj source.family
      blocks source.blockSeries p 2)
    (ordinaryBlockEquivariant : ∀ (a : TypeBSpinStabilizer.OuterGroup f)
        (x : source.family.Basic),
      ordinaryBlock Msys iota hinj source blocks ordinary (a • x) =
        a • ordinaryBlock Msys iota hinj source blocks ordinary x)
    (brauerBlockEquivariant : ∀ (a : TypeBSpinStabilizer.OuterGroup f) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (a • phi) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks phi)
    (actions : EffectiveActionSource fieldSource iota hinj source.family.selectedSeries
      (TypeBSpinConlonSplittingSourceInstantiation.spinBasicSetFromTheorem23
        Msys iota hcompat hinj source blocks
        certificate hEll hOdd hNondef))
    (b : SpinBlock (k := k) (N := N))
    (conlon : PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) b))
    (burnside : PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) b)) :
    let J := MulAction.stabilizer (TypeBSpinStabilizer.OuterGroup f) b
    let blockOf := ordinaryBlock Msys iota hinj source blocks ordinary
    let _ : MulAction J (BlockFibre blockOf b) :=
      stabilizerFibreAction blockOf ordinaryBlockEquivariant b
    let _ : MulAction J
        (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      stabilizerFibreAction (irreducibleBrauerCharacterBlock iota hinj blocks)
        brauerBlockEquivariant b
    IsPHypoelementary 2 J ∧
      Nonempty ((Representation.ofMulAction ℤ J (BlockFibre blockOf b)).Equiv
        (Representation.ofMulAction ℤ J
          (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))) ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
          BlockFibre blockOf b,
        ∀ (j : J) (phi : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b),
          e (j • phi) = j • e phi := by
  exact lemma_4_3_spin_source_instantiated rank_at_least_three hEll hOdd hNondef
    fieldSource Msys iota hcompat hinj source blocks certificate
    (ordinaryBlock Msys iota hinj source blocks ordinary)
    (forwardGenerator Msys iota hcompat hinj source blocks ordinary
      certificate hEll hOdd hNondef)
    ordinaryBlockEquivariant brauerBlockEquivariant actions b conlon burnside

end ModularRep.PaperProofs.TypeBSpinConlonPhysicalSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
