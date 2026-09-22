import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding

/-!
# The actual principal ordinary-weight cover fibres are involution orbits

On the literal `PublishedWeightCovering`, a nonsplit fibre has one point.
A split fibre has two points, and the original point and its actual SO
involution image are distinct points in it. The finite-cardinality lemmas
therefore identify every fibre with precisely that involution orbit.

No orbit matching, new covering source or Brauer-to-weight map is assumed.
The specified DGN covering relation remains bound by `covers_iff`.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalCoverOrbit

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding

local instance finiteGroupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable (F : Type) [Field F] [Finite F]
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (delta : H F) (indexTwo : (G F).index = 2)
  {r f : ℕ} [CharP F r]
  (SH : SOWeightSource (k := k) (K := K) F)
  (bH : LiteralPrimitiveBlock k (H F))
  [Fintype (OmegaWeight F S b)] [DecidableEq (SOWeight F SH bH)]
  (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
  (outside : delta ∉ G F) (hbH : IsPrincipal bH)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (dgn : WeightCoveringModel (k := k) (K := K) F)
  (covering : PublishedWeightCovering F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn)

/-- Equality in a nonsplit specified covering fibre forces equality of its points. -/
theorem eq_of_cover_eq_of_not_split (w v : OmegaWeight F S b)
    (hs : ¬ covering.splits (covering.cover w))
    (h : covering.cover w = covering.cover v) : v = w := by
  classical
  let Fibre := {a : OmegaWeight F S b // covering.cover a = covering.cover w}
  have card : Fintype.card Fibre = 1 := by
    simpa only [if_neg hs] using covering.fibre_card (covering.cover w)
  obtain ⟨only, unique⟩ := Fintype.card_eq_one_iff.mp card
  let original : Fibre := ⟨w, rfl⟩
  let candidate : Fibre := ⟨v, h.symm⟩
  exact congrArg Subtype.val ((unique candidate).trans (unique original).symm)

/-- In a split fibre the actual moved point is the unique point other than w. -/
theorem eq_or_step_of_cover_eq_of_split (w v : OmegaWeight F S b)
    (hs : covering.splits (covering.cover w))
    (h : covering.cover w = covering.cover v) :
    v = w ∨ v = weightPermutation F S literal b hb delta indexTwo w := by
  classical
  let Fibre := {a : OmegaWeight F S b // covering.cover a = covering.cover w}
  have card : Nat.card Fibre = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa only [if_pos hs] using covering.fibre_card (covering.cover w)
  let original : Fibre := ⟨w, rfl⟩
  let moved : Fibre :=
    ⟨weightPermutation F S literal b hb delta indexTwo w, covering.cover_action w⟩
  let candidate : Fibre := ⟨v, h.symm⟩
  have moved_ne : moved ≠ original := by
    intro heq
    exact covering.split_weights_are_moved w hs (congrArg Subtype.val heq)
  obtain ⟨other, _, unique⟩ := (Nat.card_eq_two_iff' original).mp card
  by_cases hv : v = w
  · exact Or.inl hv
  · have candidate_ne : candidate ≠ original := fun heq => hv (congrArg Subtype.val heq)
    exact Or.inr (congrArg Subtype.val
      ((unique candidate candidate_ne).trans (unique moved moved_ne).symm))

/-- The SAME actual covering map identifies precisely one involution orbit. -/
theorem cover_eq_iff (w v : OmegaWeight F S b) :
    covering.cover w = covering.cover v ↔
      v = w ∨ v = weightPermutation F S literal b hb delta indexTwo w := by
  classical
  constructor
  · intro h
    by_cases hs : covering.splits (covering.cover w)
    · exact eq_or_step_of_cover_eq_of_split F S literal b hb delta indexTwo SH bH
        parameters notThree outside hbH literalH dgn covering w v hs h
    · exact Or.inl (eq_of_cover_eq_of_not_split F S literal b hb delta indexTwo SH bH
        parameters notThree outside hbH literalH dgn covering w v hs h)
  · rintro (rfl | rfl)
    · rfl
    · exact (covering.cover_action w).symm

/-- The orbit statement is also on the literal local-character DGN relation. -/
theorem coversClass_cover_iff (w v : OmegaWeight F S b) :
    TypeBWeightCoveringSource.CoversClass (G F) dgn (covering.cover w).val v.val ↔
      v = w ∨ v = weightPermutation F S literal b hb delta indexTwo w := by
  rw [covering.covers_iff]
  exact eq_comm.trans (cover_eq_iff F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn covering w v)

include covering in
/-- Once an actual SO class covers w, its entire covering fibre is this orbit. -/
theorem coversClass_iff_of_covers (h : SOWeight F SH bH) (w v : OmegaWeight F S b)
    (hw : TypeBWeightCoveringSource.CoversClass (G F) dgn h.val w.val) :
    TypeBWeightCoveringSource.CoversClass (G F) dgn h.val v.val ↔
      v = w ∨ v = weightPermutation F S literal b hb delta indexTwo w := by
  have wh : covering.cover w = h := (covering.covers_iff h w).mp hw
  rw [← wh]
  exact coversClass_cover_iff F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn covering w v

end ModularRep.PaperProofs.TypeBRankThreePrincipalCoverOrbit


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
