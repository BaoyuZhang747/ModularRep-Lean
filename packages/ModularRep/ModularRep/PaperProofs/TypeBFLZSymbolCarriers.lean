import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Literal finite-row Lusztig symbols and hook/cohook removal

Rows are actual finite subsets of the natural numbers. A symbol is the
quotient by row interchange and simultaneous beta-set shift. Rank is the
integer-part formula in Olsson, section 5, printed page 35; defect is the
absolute difference of the two row cardinalities. Both descend to the
quotient, including the empty-row case.

Hook and cohook removal are literal moves of an entry j to j-e in the same
or opposite row. The quotient relation allows actual representatives on
which that move is possible. Every such move preserves odd defect, so no
sequence from an odd-defect symbol can reach an equal-row symbol.

There is no terminal-core existence or uniqueness input in this file and
no character, block, or Type B target predicate.
-/

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZSymbolCarriers

open scoped BigOperators

/-- An ordered representative of the eventual unordered symbol. -/
abbrev Rows := Finset ℕ × Finset ℕ

/-- The ordinary one-step beta-set shift, including the new entry zero. -/
def betaShift (X : Finset ℕ) : Finset ℕ :=
  insert 0 (X.map ⟨Nat.succ, Nat.succ_injective⟩)

@[simp]
theorem zero_not_mem_shifted (X : Finset ℕ) :
    0 ∉ X.map ⟨Nat.succ, Nat.succ_injective⟩ := by simp

@[simp]
theorem betaShift_card (X : Finset ℕ) : (betaShift X).card = X.card + 1 := by
  simp [betaShift]

@[simp]
theorem betaShift_sum (X : Finset ℕ) :
    ∑ j ∈ betaShift X, j = (∑ j ∈ X, j) + X.card := by
  simp [betaShift, Finset.sum_map, Nat.succ_eq_add_one, Finset.sum_add_distrib]

def swap (R : Rows) : Rows := (R.2, R.1)

def shift (R : Rows) : Rows := (betaShift R.1, betaShift R.2)

def rowSize (R : Rows) : ℕ := R.1.card + R.2.card

def rowSum (R : Rows) : ℕ := (∑ j ∈ R.1, j) + ∑ j ∈ R.2, j

/-- Floor of ((t-1)/2)^2. At t=0 both the literal integer formula and this
natural-number formula are zero, since floor(1/4)=0. -/
def rankCorrection (t : ℕ) : ℕ := (t - 1) ^ 2 / 4

theorem rankCorrection_add_two (t : ℕ) :
    rankCorrection (t + 2) = rankCorrection t + t := by
  cases t with
  | zero => norm_num [rankCorrection]
  | succ n =>
      change (n + 2) ^ 2 / 4 = n ^ 2 / 4 + (n + 1)
      have hs : (n + 2) ^ 2 = n ^ 2 + (n + 1) * 4 := by ring
      rw [hs, Nat.add_mul_div_right _ _ (by decide : 0 < 4)]

def rowRank (R : Rows) : ℕ := rowSum R - rankCorrection (rowSize R)

/-- Absolute cardinal difference, expressed without an integer coercion. -/
def rowDefect (R : Rows) : ℕ :=
  (R.1.card - R.2.card) + (R.2.card - R.1.card)

@[simp]
theorem rowSize_shift (R : Rows) : rowSize (shift R) = rowSize R + 2 := by
  simp only [rowSize, shift, betaShift_card]
  omega

@[simp]
theorem rowSum_shift (R : Rows) : rowSum (shift R) = rowSum R + rowSize R := by
  simp only [rowSum, rowSize, shift, betaShift_sum]
  omega

@[simp]
theorem rowRank_shift (R : Rows) : rowRank (shift R) = rowRank R := by
  simp only [rowRank, rowSize_shift, rowSum_shift, rankCorrection_add_two]
  omega

@[simp]
theorem rowRank_swap (R : Rows) : rowRank (swap R) = rowRank R := by
  simp [rowRank, rowSum, rowSize, swap, Nat.add_comm]

@[simp]
theorem rowDefect_shift (R : Rows) : rowDefect (shift R) = rowDefect R := by
  simp only [rowDefect, shift, betaShift_card]
  omega

@[simp]
theorem rowDefect_swap (R : Rows) : rowDefect (swap R) = rowDefect R := by
  simp [rowDefect, swap, Nat.add_comm]

theorem rowDefect_odd_iff (R : Rows) : Odd (rowDefect R) ↔ Odd (rowSize R) := by
  simp only [Nat.odd_iff, rowDefect, rowSize]
  omega

/-- The generating identifications. Quot takes their equivalence closure,
so all simultaneous iterated shifts and unordered-row identifications hold. -/
inductive Identifies : Rows → Rows → Prop
  | swap (R : Rows) : Identifies R (swap R)
  | shift (R : Rows) : Identifies R (shift R)

def Symbol := Quot Identifies

def ofRows (R : Rows) : Symbol := Quot.mk Identifies R

theorem ofRows_eq_iff (R T : Rows) :
    ofRows R = ofRows T ↔ Relation.EqvGen Identifies R T :=
  ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

@[simp]
theorem ofRows_swap (R : Rows) : ofRows (swap R) = ofRows R :=
  (Quot.sound (Identifies.swap R)).symm

@[simp]
theorem ofRows_shift (R : Rows) : ofRows (shift R) = ofRows R :=
  (Quot.sound (Identifies.shift R)).symm

def rank : Symbol → ℕ := Quot.lift rowRank (by
  intro R T h
  cases h with
  | swap => exact (rowRank_swap R).symm
  | shift => exact (rowRank_shift R).symm)

def defect : Symbol → ℕ := Quot.lift rowDefect (by
  intro R T h
  cases h with
  | swap => exact (rowDefect_swap R).symm
  | shift => exact (rowDefect_shift R).symm)

@[simp]
theorem rank_ofRows (R : Rows) : rank (ofRows R) =
    ((∑ j ∈ R.1, j) + ∑ j ∈ R.2, j) -
      (R.1.card + R.2.card - 1) ^ 2 / 4 := rfl

@[simp]
theorem defect_ofRows (R : Rows) : defect (ofRows R) =
    (R.1.card - R.2.card) + (R.2.card - R.1.card) := rfl

@[simp]
theorem rank_empty : rank (ofRows (∅, ∅)) = 0 := by simp

@[simp]
theorem defect_empty : defect (ofRows (∅, ∅)) = 0 := by simp

/-- Odd-defect symbols, without a fixed rank. Core extraction stays in this
carrier although removal can change the rank. -/
def OddSymbol := {S : Symbol // Odd (defect S)}

/-- The exact symbol label carrier used for a symplectic component of
given rank. No duplicate decoration of degenerate symbols is added. -/
def OddRankSymbol (n : ℕ) := {S : Symbol // rank S = n ∧ Odd (defect S)}

/-- Equal rows in an actual representative, not merely equal row lengths. -/
def Degenerate (S : Symbol) : Prop := ∃ X : Finset ℕ, ofRows (X, X) = S

theorem degenerate_defect_zero {S : Symbol} (h : Degenerate S) : defect S = 0 := by
  rcases h with ⟨X, rfl⟩
  simp

theorem odd_defect_not_degenerate {S : Symbol} (h : Odd (defect S)) : ¬ Degenerate S := by
  intro hdeg
  have hz := degenerate_defect_zero hdeg
  rw [hz] at h
  exact (by decide : ¬ Odd (0 : ℕ)) h

theorem oddRankSymbol_not_degenerate {n : ℕ} (S : OddRankSymbol n) :
    ¬ Degenerate S.val := odd_defect_not_degenerate S.property.2

inductive RemovalKind
  | hook
  | cohook
  deriving DecidableEq

/-- Literal positive-length removal. The destination is absent in the
original destination row, as in the beta-set hook/cohook definition. -/
inductive RowRemoval (e : ℕ) : RemovalKind → Rows → Rows → Prop
  | hook_left (X Y : Finset ℕ) (j : ℕ) (positive : 0 < e)
      (present : j ∈ X) (large : e ≤ j) (absent : j - e ∉ X) :
      RowRemoval e .hook (X, Y) (insert (j - e) (X.erase j), Y)
  | hook_right (X Y : Finset ℕ) (j : ℕ) (positive : 0 < e)
      (present : j ∈ Y) (large : e ≤ j) (absent : j - e ∉ Y) :
      RowRemoval e .hook (X, Y) (X, insert (j - e) (Y.erase j))
  | cohook_left (X Y : Finset ℕ) (j : ℕ) (positive : 0 < e)
      (present : j ∈ X) (large : e ≤ j) (absent : j - e ∉ Y) :
      RowRemoval e .cohook (X, Y) (X.erase j, insert (j - e) Y)
  | cohook_right (X Y : Finset ℕ) (j : ℕ) (positive : 0 < e)
      (present : j ∈ Y) (large : e ≤ j) (absent : j - e ∉ X) :
      RowRemoval e .cohook (X, Y) (insert (j - e) X, Y.erase j)

private theorem moved_card (X : Finset ℕ) (a b : ℕ) (ha : a ∈ X) (hb : b ∉ X) :
    (insert b (X.erase a)).card = X.card := by
  have hnot : b ∉ X.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem ha]
  have hpos : 0 < X.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega

theorem RowRemoval.rowSize_eq {e : ℕ} {kind : RemovalKind} {R T : Rows}
    (h : RowRemoval e kind R T) : rowSize T = rowSize R := by
  cases h with
  | hook_left X Y j he hj hle hn =>
      simp only [rowSize, moved_card X j (j - e) hj hn]
  | hook_right X Y j he hj hle hn =>
      simp only [rowSize, moved_card Y j (j - e) hj hn]
  | cohook_left X Y j he hj hle hn =>
      have hpos : 0 < X.card := Finset.card_pos.mpr ⟨j, hj⟩
      simp only [rowSize, Finset.card_erase_of_mem hj, Finset.card_insert_of_notMem hn]
      omega
  | cohook_right X Y j he hj hle hn =>
      have hpos : 0 < Y.card := Finset.card_pos.mpr ⟨j, hj⟩
      simp only [rowSize, Finset.card_erase_of_mem hj, Finset.card_insert_of_notMem hn]
      omega

theorem RowRemoval.hook_defect_eq {e : ℕ} {R T : Rows}
    (h : RowRemoval e .hook R T) : rowDefect T = rowDefect R := by
  cases h with
  | hook_left X Y j he hj hle hn =>
      simp only [rowDefect, moved_card X j (j - e) hj hn]
  | hook_right X Y j he hj hle hn =>
      simp only [rowDefect, moved_card Y j (j - e) hj hn]

theorem RowRemoval.odd_defect_iff {e : ℕ} {kind : RemovalKind} {R T : Rows}
    (h : RowRemoval e kind R T) : Odd (rowDefect T) ↔ Odd (rowDefect R) := by
  rw [rowDefect_odd_iff, rowDefect_odd_iff, h.rowSize_eq]

/-- An actual removal on some representatives of the two quotient symbols. -/
def Removes (kind : RemovalKind) (e : ℕ) (S T : Symbol) : Prop :=
  ∃ R U : Rows, ofRows R = S ∧ ofRows U = T ∧ RowRemoval e kind R U

theorem Removes.odd_defect_iff {kind : RemovalKind} {e : ℕ} {S T : Symbol}
    (h : Removes kind e S T) : Odd (defect T) ↔ Odd (defect S) := by
  rcases h with ⟨R, U, rfl, rfl, hRU⟩
  exact hRU.odd_defect_iff

theorem Removes.hook_defect_eq {e : ℕ} {S T : Symbol}
    (h : Removes .hook e S T) : defect T = defect S := by
  rcases h with ⟨R, U, rfl, rfl, hRU⟩
  exact hRU.hook_defect_eq

def RemovesStar (kind : RemovalKind) (e : ℕ) : Symbol → Symbol → Prop :=
  Relation.ReflTransGen (Removes kind e)

theorem RemovesStar.odd_defect_iff {kind : RemovalKind} {e : ℕ} {S T : Symbol}
    (h : RemovesStar kind e S T) : Odd (defect T) ↔ Odd (defect S) := by
  induction h with
  | refl => rfl
  | tail hst htu ih => exact htu.odd_defect_iff.trans ih

theorem RemovesStar.not_degenerate {kind : RemovalKind} {e : ℕ} {S T : Symbol}
    (h : RemovesStar kind e S T) (hodd : Odd (defect S)) : ¬ Degenerate T :=
  odd_defect_not_degenerate (h.odd_defect_iff.mpr hodd)

/-- Being terminal is defined from the literal removal relation. Existence
and uniqueness of a reachable terminal symbol are not assumed here. -/
def Terminal (kind : RemovalKind) (e : ℕ) (S : Symbol) : Prop :=
  ∀ T : Symbol, ¬ Removes kind e S T

end ModularRep.PaperProofs.TypeBFLZSymbolCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
