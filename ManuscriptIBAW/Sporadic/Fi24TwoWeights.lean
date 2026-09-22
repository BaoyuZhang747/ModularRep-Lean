import ManuscriptIBAW.Sporadic.Fi24TwoSupport
import ManuscriptIBAW.Sporadic.Fi24TwoCounting

/-!
# The two nonprincipal weight signatures at two

The subgroup classification places the weights in the specified radical
rows. The finite invariant subset argument then gives the signatures for the
V4_b and D8 blocks. Sambale's theorem supplies only the numerical block
sizes. No local character allocation obtained from fusion is assumed.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ManuscriptIBAW.Sporadic.Fi24TwoWeights
open ModularRep ModularRep.CharacterWeight ModularRep.PaperProofs
open ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierActualTwoActions
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open Fi24TwoRows Fi24TwoSupport Fi24TwoCounting

universe u v
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subFinite (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFinite : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {BIndex : Type u} [Fintype BIndex] {e : BIndex → k[X]}
variable (blocks : BlockIdempotentDecomposition e)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (tau : MulAut X) {Row : Fin 34 → Type v} [∀ i, Finite (Row i)] {BlockD : Type u}
variable [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
variable (T : TrivialOrdinaryTableData iota tau Row BlockD)
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (roles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
variable (geometry : Geometry iota R T roles)
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
variable (Dzero : DefectZeroReductionSource iota) (Tzero : TrivialWeightSource (p := 2) (X := X))
variable (hsingle : ∀ d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := X),
  Subsingleton {phi : IBr iota // brauerBlock iota hinj blocks phi = D.ordinaryBlock d.1})

include compatibility in
theorem c2_empty (w : WeightClass (p := 2) (K := K) (X := X)) :
    ¬ row R (classOf T (geometry.index 0)) w := by
  intro hw
  have := row_finite R T compatibility (geometry.index 0)
  have hp : 0 < Nat.card {w // row R (classOf T (geometry.index 0)) w} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨w, hw⟩⟩, inferInstance⟩
  have hc := row_total R T compatibility (geometry.index 0)
  rw [geometry.entry] at hc
  norm_num [SporadicProposition57ComputationRelative.TableSignatureEntry.total] at hc
  omega

include compatibility D C Dzero Tzero hsingle in
theorem klein_support
    (hcard : Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (roles 1).1} = 3)
    (w : WeightClass (p := 2) (K := K) (X := X))
    (hw : R.1.weightBlock w = (roles 1).1) :
    row R (classOf T (geometry.index 2)) w := by
  have hs : weightSector (R := R) w = 1 := by
    change blockSector (R.1.weightBlock w) = 1
    rw [hw]
    exact (roles 1).2
  revert hw hs
  refine Quotient.inductionOn w ?_
  intro w
  refine Quotient.inductionOn w ?_
  intro W hw hs
  let Q : CharacterWeight.RadicalSubgroup (p := 2) (G := X) := ⟨W.subgroup, W.radical⟩
  have hsub := raw_subconjugate iota R compatibility (roles 1).1 geometry.D4
    geometry.defect4 W (C W) hw
  rcases geometry.klein Q hsub with hbot | hc2 | hv
  · exact (raw_not_bot iota R hinj blocks D C Dzero Tzero hsingle compatibility
      (roles 1).1 hcard W hw hbot).elim
  · exact (c2_empty iota R tau T compatibility roles geometry _ ⟨hs, hc2⟩).elim
  · exact ⟨hs, hv⟩

include compatibility D C Dzero Tzero hsingle in
theorem dihedral_support
    (hcard : Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (roles 2).1} = 3)
    (w : WeightClass (p := 2) (K := K) (X := X))
    (hw : R.1.weightBlock w = (roles 2).1) :
    row R (classOf T (geometry.index 1)) w ∨
      row R (classOf T (geometry.index 2)) w ∨ row R (classOf T (geometry.index 3)) w := by
  have hs : weightSector (R := R) w = 1 := by
    change blockSector (R.1.weightBlock w) = 1
    rw [hw]
    exact (roles 2).2
  revert hw hs
  refine Quotient.inductionOn w ?_
  intro w
  refine Quotient.inductionOn w ?_
  intro W hw hs
  let Q : CharacterWeight.RadicalSubgroup (p := 2) (G := X) := ⟨W.subgroup, W.radical⟩
  have hsub := raw_subconjugate iota R compatibility (roles 2).1 geometry.D8
    geometry.defect8 W (C W) hw
  rcases geometry.dihedral Q hsub with hbot | hc2 | ha | hb | hd
  · exact (raw_not_bot iota R hinj blocks D C Dzero Tzero hsingle compatibility
      (roles 2).1 hcard W hw hbot).elim
  · exact (c2_empty iota R tau T compatibility roles geometry _ ⟨hs, hc2⟩).elim
  · exact Or.inl ⟨hs, ha⟩
  · exact Or.inr (Or.inl ⟨hs, hb⟩)
  · exact Or.inr (Or.inr ⟨hs, hd⟩)

include compatibility in
theorem possible_counts :
    Nat.card {w // row R (classOf T (geometry.index 1)) w ∨
      row R (classOf T (geometry.index 2)) w ∨ row R (classOf T (geometry.index 3)) w} = 6 ∧
    Nat.card {w // (row R (classOf T (geometry.index 1)) w ∨
      row R (classOf T (geometry.index 2)) w ∨ row R (classOf T (geometry.index 3)) w) ∧
        MulOpposite.op tau • w = w} = 4 := by
  classical
  let P (j : Fin 4) := row R (classOf T (geometry.index j))
  have finite (j : Fin 4) : Finite {w // P j w} := row_finite R T compatibility _
  have disjoint (a b : Fin 4) (hab : a ≠ b) (w) (ha : P a w) (hb : P b w) : False :=
    hab (geometry.index_injective ((classOf_injective T) (ha.2.symm.trans hb.2)))
  have total (j : Fin 4) := row_total R T compatibility (geometry.index j)
  have fixedCount (j : Fin 4) := row_fixed R T compatibility (geometry.index j)
  have := finite 1
  have := finite 2
  have := finite 3
  constructor
  · have h := card_three_rows (P 1) (P 2) (P 3)
      (disjoint 1 2 (by decide)) (disjoint 1 3 (by decide)) (disjoint 2 3 (by decide))
    simpa [P, total, geometry.entry,
      SporadicProposition57ComputationRelative.TableSignatureEntry.total] using h
  · let f := fun w : WeightClass (p := 2) (K := K) (X := X) => MulOpposite.op tau • w = w
    have finiteFixed (j : Fin 4) : Finite {w // P j w ∧ f w} :=
      Finite.of_injective (fun w : {w // P j w ∧ f w} => (⟨w.1, w.2.1⟩ : {w // P j w}))
        (fun _ _ h => Subtype.ext (congrArg (fun w : {w // P j w} => w.1) h))
    have := finiteFixed 1
    have := finiteFixed 2
    have := finiteFixed 3
    have h := card_three_rows (fun w => P 1 w ∧ f w) (fun w => P 2 w ∧ f w)
      (fun w => P 3 w ∧ f w)
      (fun w ha hb => disjoint 1 2 (by decide) w ha.1 hb.1)
      (fun w ha hb => disjoint 1 3 (by decide) w ha.1 hb.1)
      (fun w ha hb => disjoint 2 3 (by decide) w ha.1 hb.1)
    have he : Nat.card {w // (P 1 w ∨ P 2 w ∨ P 3 w) ∧ f w} =
        Nat.card {w // (P 1 w ∧ f w) ∨ (P 2 w ∧ f w) ∨ (P 3 w ∧ f w)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun _ => by tauto))
    rw [he, h]
    change Nat.card {w // row R (classOf T (geometry.index 1)) w ∧ MulOpposite.op tau • w = w} +
      Nat.card {w // row R (classOf T (geometry.index 2)) w ∧ MulOpposite.op tau • w = w} +
      Nat.card {w // row R (classOf T (geometry.index 3)) w ∧ MulOpposite.op tau • w = w} = 4
    rw [fixedCount, fixedCount, fixedCount, geometry.entry, geometry.entry, geometry.entry]
    decide

include T geometry compatibility D C Dzero Tzero hsingle in
theorem fixed_counts
    (decomposition : ∀ a : MulAut X, ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hBrOther : ∀ j : Fin 4, actualBrauerSignature iota hinj blocks tau (roles j.succ).1 = nonprincipalSignature j)
    (small : SmallDefectNumericalSource iota hinj R)
    (hDefect : ∀ j : Fin 4, ∃ H : Subgroup X, actualHasDefect R (roles j.succ).1 H ∧
      Nat.card H = (if j = 0 then 4 else if j = 1 then 8 else 1)) :
    Nat.card {w // R.1.weightBlock w = (roles 1).1 ∧ MulOpposite.op tau • w = w} = 1 ∧
      Nat.card {w // R.1.weightBlock w = (roles 2).1 ∧ MulOpposite.op tau • w = w} = 3 := by
  classical
  have htot := nonprincipal_weight_totals iota hinj blocks R tau roles hBrOther small hDefect
  have hstable := nonprincipal_blocks_fixed iota hinj blocks tau roles hBrOther
  have hp := possible_counts iota R tau T compatibility roles geometry
  apply predicate_counts (fun w : WeightClass (p := 2) (K := K) (X := X) => MulOpposite.op tau • w)
    (weight_tau_involutive (p := 2) (K := K) tau decomposition)
    (fun w => R.1.weightBlock w = (roles 1).1) (fun w => R.1.weightBlock w = (roles 2).1)
    (row R (classOf T (geometry.index 2)))
    (fun w => row R (classOf T (geometry.index 1)) w ∨
      row R (classOf T (geometry.index 2)) w ∨ row R (classOf T (geometry.index 3)) w)
  · intro w hw
    rw [R.1.weightBlock_transport, hw]
    exact hstable 0
  · exact row_stable R T (geometry.index 2)
  · exact klein_support iota hinj blocks R tau T compatibility roles geometry D C Dzero Tzero hsingle
      (congrArg Prod.fst (hBrOther 0))
  · exact fun _ h => Or.inr (Or.inl h)
  · exact dihedral_support iota hinj blocks R tau T compatibility roles geometry D C Dzero Tzero hsingle
      (congrArg Prod.fst (hBrOther 1))
  · intro w hw hp
    have he : (roles 2).1 = (roles 1).1 := hw.symm.trans hp
    have := roles.injective (Subtype.ext he)
    exact (by decide : (2 : Fin 5) ≠ 1) this
  · exact htot 0
  · exact htot 1
  · rw [row_total R T compatibility, geometry.entry]
    decide
  · rw [row_fixed R T compatibility, geometry.entry]
    decide
  · exact hp.1
  · exact hp.2

end ManuscriptIBAW.Sporadic.Fi24TwoWeights

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
