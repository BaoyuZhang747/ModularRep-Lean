import ManuscriptIBAW.Sporadic.Fi24TwoRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRawBrauerSupport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts

/-! The local geometry concerns actual radical subgroups inside actual
defect groups. It contains no assignment of local characters to blocks. -/

noncomputable section
open scoped MonoidAlgebra
namespace ManuscriptIBAW.Sporadic.Fi24TwoSupport
open ModularRep ModularRep.CharacterWeight ModularRep.PaperProofs
open ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalRawBrauerSupport
open SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
open SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open Fi24TwoRows

universe u v
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subFinite (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFinite : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
local instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable {tau : MulAut X} {Row : Fin 34 → Type v} {BlockD : Type u}
variable [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]

/-- An–Cannon–O'Brien–Unger, Lemma 4.2(d), together with the radical subgroup
classification and the four specified Table 8 entries with the stated
corrections. Indices 0, 1, 2 and 3 denote C2, V4_a, V4_b and D8. The
universal statements in `klein` and `dihedral` concern subgroups and assume
no allocation of local ordinary characters to blocks. -/
structure Geometry (T : TrivialOrdinaryTableData iota tau Row BlockD)
    (roles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1}) where
  index : Fin 4 → Fin 34
  index_injective : Function.Injective index
  entry : ∀ j, T.entry (index j) =
    (if j = 0 then ⟨0, 0⟩ else if j = 2 then ⟨2, 2⟩ else ⟨1, 0⟩)
  D4 : Subgroup X
  D8 : Subgroup X
  defect4 : actualHasDefect R (roles 1).1 D4
  defect8 : actualHasDefect R (roles 2).1 D8
  order4 : Nat.card D4 = 4
  order8 : Nat.card D8 = 8
  klein : ∀ Q : CharacterWeight.RadicalSubgroup (p := 2) (G := X),
    Q.1.IsSubconjugate D4 → Q.1 = ⊥ ∨
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X)) = classOf T (index 0) ∨
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X)) = classOf T (index 2)
  dihedral : ∀ Q : CharacterWeight.RadicalSubgroup (p := 2) (G := X),
    Q.1.IsSubconjugate D8 → Q.1 = ⊥ ∨
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X)) = classOf T (index 0) ∨
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X)) = classOf T (index 1) ∨
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X)) = classOf T (index 2) ∨
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X)) = classOf T (index 3)

theorem raw_subconjugate
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (b : ActualBlock (k := k) (X := X)) (D : Subgroup X)
    (hD : actualHasDefect R b D) (W : CharacterWeight 2 K X)
    (C : CanonicalRawReduction iota W) (hW : R.1.operations.rawWeightBlock W = b) :
    W.subgroup.IsSubconjugate D := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  have hs := rawWeight_has_nonzero_brauer_support iota R compatibility W C
  rw [hW] at hs
  exact (hD.support411.nonzero_iff_isSubconjugate W.subgroup W.radical.isPGroup).mp hs

/-- A weight with trivial radical cannot belong to a block with three Brauer
characters. Canonical reduction and the singleton law for ordinary defect
zero blocks give a contradiction before constructing a correspondence. -/
theorem raw_not_bot
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {BIndex : Type u} [Fintype BIndex] {e : BIndex → k[X]}
    (blocks : BlockIdempotentDecomposition e)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
    (Dzero : DefectZeroReductionSource iota) (Tzero : TrivialWeightSource (p := 2) (X := X))
    (hsingle : ∀ d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := X),
      Subsingleton {phi : IBr iota // brauerBlock iota hinj blocks phi = D.ordinaryBlock d.1})
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (b : ActualBlock (k := k) (X := X))
    (hcard : Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} = 3)
    (W : CharacterWeight 2 K X) (hW : R.1.operations.rawWeightBlock W = b) :
    W.subgroup ≠ ⊥ := by
  intro hbot
  let w : WeightClass (p := 2) (K := K) (X := X) := Quotient.mk'' (Quotient.mk'' W)
  have htrivial : radicalClass w = RadicalConjugacyClass.trivialClass Tzero.trivialRadical :=
    congrArg Quotient.mk'' (Subtype.ext hbot)
  obtain ⟨d, hd⟩ := Tzero.exists_atOne_of_radicalClass_eq_trivial w htrivial
  let := R.1.operations.ambientBlockData.fintypeBlock
  have hcanonical := (trivialWeightBlockCompatibilityOfCanonicalOperations
    iota hinj R C Dzero Tzero compatibility).block_atOne d
  have hb : b = D.ordinaryBlock d.1 := by
    calc
      b = R.1.weightBlock w := hW.symm
      _ = R.1.weightBlock (Tzero.atOne d) := congrArg R.1.weightBlock hd.symm
      _ = _ := hcanonical
      _ = D.ordinaryBlock d.1 := canonicalBrauerBlock_reduce_eq_ordinaryBlock
        iota hinj blocks R D Dzero d
  have : Subsingleton {phi : IBr iota // brauerBlock iota hinj blocks phi = b} := by
    rw [hb]
    exact hsingle d
  have hn : Nonempty {phi : IBr iota // brauerBlock iota hinj blocks phi = b} :=
    (Nat.card_pos_iff.mp (by omega)).1
  have hle := Nat.card_of_subsingleton (Classical.choice hn)
  omega

end ManuscriptIBAW.Sporadic.Fi24TwoSupport

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
