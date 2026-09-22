import ModularRep.PaperProofs.TypeBSpinDiagonalNormSource
import ModularRep.PaperProofs.TypeBSpinConlonEffectiveActionInstantiation

/-!
# Spin Lemma 4.2 with the diagonal map constructed from the norm

The actual norm-square-class map replaces the former diagonal-source input.
The centre statement is the narrow, canonically matched external structural
input on the same odd-dimensional finite Clifford carrier. All character,
block, integral-series and Conlon deductions are reused without changing
carriers or importing the desired conclusion as an input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinConlonNormSourceInstantiation

open ModularRep BlockFibreRestriction FDRepSimpleClassKZero IntegralBasicSetBridge
open OrdinaryIrreducibleCharacter ConlonBasicSet
open TypeBCliffordCarriers TypeBSpinStabilizer TypeBSpinDiagonalFieldQuotient
open TypeBSpinConlonBlockSourceInstantiation TypeBSpinConlonPhysicalSourceInstantiation
open TypeBSpinEffectiveSourceBinding TypeBIntegralSeriesSplitting
open TypeBCliffordCentreSource TypeBSpinDiagonalNormSource
open TypeBSpinConlonEffectiveActionInstantiation

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} [Finite (Spin n F N)]
  [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- The same Spin Conlon conclusion with its literal diagonal quotient computed
from the actual norm and the matched one-way centre certificate. -/
theorem lemma_4_3_spin_norm_source_instantiated
    (rank_at_least_three : 3 ≤ n)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    {parameters : OddFieldParameters F p f}
    (fs : FieldActionSource n F p f parameters N)
    (centre : CentreSource n F parameters
      (Nat.le_trans (by decide : 1 ≤ 3) rank_at_least_three))
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Finite source.family.Basic]
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
    let D := diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) rank_at_least_three) centre
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
          e (j • phi) = j • e phi := by
  dsimp only
  exact lemma_4_3_spin_effective_action_instantiated rank_at_least_three hEll hOdd hNondef
    fs (diagonalSource n F N parameters
      (Nat.le_trans (by decide : 1 ≤ 3) rank_at_least_three) centre)
    Msys iota hcompat hinj source blocks ordinary certificate diagonalStable fieldStable b

end ModularRep.PaperProofs.TypeBSpinConlonNormSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
