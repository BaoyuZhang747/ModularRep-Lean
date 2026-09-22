import ModularRep.PaperProofs.TypeBSpinConlonNormSourceInstantiation
import ModularRep.PaperProofs.TypeBSpinBroueMichelSourceBinding
import ModularRep.PaperProofs.TypeBSpinRationalIndexAction

/-!
# Spin Conlon endpoint with the full Broue--Michel source binding

The full PCSp rational family determines the selected series and the block
assignment. The individual FLZ map is supplied on the literal specified
Brauer union and transported through the proved block-index identification.
Per-series diagonal and positive dual-field naturality imply the exact
selected callbacks. The actual norm diagonal and all checked Conlon
deductions are reused.

This is conditional on the explicitly prescribed full Lusztig-family
meaning, ordinary partition/specified block theorem, nonzero columns, exact
individual FLZ packet, naturality, and the existing structural/root inputs.
No source states the blockwise bijection or any BAW/iBAW conclusion.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinConlonBroueMichelInstantiation

open ModularRep BlockFibreRestriction FDRepSimpleClassKZero IntegralBasicSetBridge
open OrdinaryIrreducibleCharacter ConlonBasicSet
open TypeBCliffordCarriers TypeBSpinStabilizer TypeBSpinDiagonalFieldQuotient
open TypeBSpinConlonBlockSourceInstantiation TypeBSpinConlonPhysicalSourceInstantiation
open TypeBSpinEffectiveSourceBinding TypeBIntegralSeriesSplitting
open TypeBCliffordCentreSource TypeBSpinDiagonalNormSource
open TypeBSpinConlonNormSourceInstantiation TypeBSpinBroueMichelSourceBinding
open TypeBSpinBroueMichelCarriers TypeBSpinRationalIndexAction TypeBRationalSeriesSource

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} [Finite (Spin n F N)]
  [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- The same actual Spin block-lattice and equivariant-bijection conclusion
with the independent block assignment and selected-stability inputs removed. -/
theorem lemma_4_3_spin_broue_michel_instantiated
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
    (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F))
    [Finite (selectedFamily (ell := ell) S).Basic]
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks)
    (unionSource : BlockUnionCertificate S parameters.prime hEll hNondef
      Msys iota hinj blocks ordinary)
    (existsAbove : ∀ phi : IBr iota, ∃ chi : Irr K (Spin n F N),
      TypeBOrdinaryBlockSplitting.decompositionNumber Msys iota chi phi ≠ 0)
    (certificate : LiteralTheorem23Certificate S parameters.prime hEll hNondef
      Msys iota hinj hcompat)
    (diagonalNatural : ∀ (g : SpecialClifford n F) (i : FullRationalIndex p n F)
      (chi : Irr K (Spin n F N)), chi ∈ S.rationalSeries i →
        OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
          (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) ∈ S.rationalSeries i)
    (fieldNatural : ∀ (e : FieldGroup f) (i : FullRationalIndex p n F)
      (chi : Irr K (Spin n F N)), chi ∈ S.rationalSeries i →
        OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi (spinFieldAction n F fs e⁻¹)
          ∈ S.rationalSeries (fullIndexMap
            (TypeBConformalDualFieldAction.pcspFieldAction F n parameters e) i))
    (b : SpinBlock (k := k) (N := N)) :
    let source := rationalSource S parameters.prime hEll hNondef
      Msys iota hinj blocks ordinary unionSource
    let diagonalStable := selected_diagonal_stable S diagonalNatural
    let fieldStable := selected_field_stable parameters fs S fieldNatural
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
  letI : Finite (rationalSource S parameters.prime hEll hNondef
      Msys iota hinj blocks ordinary unionSource).family.Basic := by
    change Finite (selectedFamily (ell := ell) S).Basic
    infer_instance
  dsimp only
  exact lemma_4_3_spin_norm_source_instantiated rank_at_least_three hEll hOdd hNondef
    fs centre Msys iota hcompat hinj
    (rationalSource S parameters.prime hEll hNondef Msys iota hinj blocks ordinary unionSource)
    blocks ordinary
    (theorem23Certificate S parameters.prime hEll hNondef Msys iota hinj blocks ordinary
      unionSource hcompat existsAbove certificate)
    (selected_diagonal_stable S diagonalNatural)
    (selected_field_stable parameters fs S fieldNatural) b

end ModularRep.PaperProofs.TypeBSpinConlonBroueMichelInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
