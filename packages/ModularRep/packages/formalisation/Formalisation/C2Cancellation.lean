import Mathlib

/-!
# Cancellation for finite `C₂`-sets

This file formalises the self-contained finite set core of the cancellation
lemma used in the sporadic section of the manuscript.  For an actual
involution of a finite type, `card_eq_fixed_add_twice_cycleCount` proves that
the total cardinality is the fixed point count plus twice the number of
nontrivial cycles.  The theorem
`exists_equivariantEquiv_of_card_eq_of_fixed_card_eq` proves that equal total
and fixed point counts give an equivariant equivalence.  Thus it verifies the
classification of finite `C₂`-sets used in the manuscript.

`C2OrbitData` stores the numbers of singleton and two element orbits.
Coordinatewise addition represents disjoint union.

The theorem `cancel_decomposition` verifies the cancellation step after the
orbit classification has been made.  The last two theorems verify, in the
standard model for two blocks exchanged by the involution, that a bijection
chosen on one block extends equivariantly and preserves the two block labels.

No representation theoretic assertion is formalised here: in particular, the
file does not establish that the character and weight sets in the manuscript
have the stated orbit data, nor that their parts belong to the asserted
blocks.
-/

namespace Formalisation.C2Cancellation

/-- The complete orbit invariant of a finite `C₂`-set: the number of
singleton orbits and the number of two element orbits. -/
abbrev C2OrbitData := ℕ × ℕ

/-- The number of singleton orbits. -/
def fixedOrbits (d : C2OrbitData) : ℕ := d.1

/-- The number of orbits of size two. -/
def twoElementOrbits (d : C2OrbitData) : ℕ := d.2

/-- The total number of orbits. -/
def orbitCount (d : C2OrbitData) : ℕ := fixedOrbits d + twoElementOrbits d

/-- The cardinality of a finite `C₂`-set with orbit data `d`. -/
def card (d : C2OrbitData) : ℕ := fixedOrbits d + 2 * twoElementOrbits d

/-- The signature used in the manuscript: total cardinality followed by the
number of fixed points. -/
def signature (d : C2OrbitData) : ℕ × ℕ := (card d, fixedOrbits d)

@[simp] theorem fixedOrbits_add (d e : C2OrbitData) :
    fixedOrbits (d + e) = fixedOrbits d + fixedOrbits e := rfl

@[simp] theorem twoElementOrbits_add (d e : C2OrbitData) :
    twoElementOrbits (d + e) = twoElementOrbits d + twoElementOrbits e := rfl

@[simp] theorem card_add (d e : C2OrbitData) : card (d + e) = card d + card e := by
  simp only [card, fixedOrbits_add, twoElementOrbits_add]
  omega

/-- Total cardinality and the number of fixed points determine the orbit data
of a finite `C₂`-set. -/
theorem orbitData_eq_of_card_eq_of_fixed_eq {d e : C2OrbitData}
    (hcard : card d = card e) (hfixed : fixedOrbits d = fixedOrbits e) : d = e := by
  apply Prod.ext hfixed
  dsimp [card, fixedOrbits, twoElementOrbits] at hcard hfixed ⊢
  omega

/-- Equivalently, the signature is a complete invariant of finite `C₂`-sets
once they are represented by their orbit data. -/
theorem signature_injective : Function.Injective signature := by
  intro d e h
  apply orbitData_eq_of_card_eq_of_fixed_eq
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- The fixed-point count can be recovered from the total cardinality and
the number of orbits.  This is the arithmetic identity behind the formula
"twice the second rank minus the first" in the computational appendix, once
those two ranks have been identified with the orbit count and total count. -/
theorem fixedOrbits_eq_twice_orbitCount_sub_card (d : C2OrbitData) :
    fixedOrbits d = 2 * orbitCount d - card d := by
  rcases d with ⟨fixed, pairs⟩
  simp only [fixedOrbits, orbitCount, twoElementOrbits, card]
  omega

section ActualFiniteInvolutions

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Conjugating a permutation along an equivalence carries its fixed points
bijectively to the fixed points of the conjugated permutation. -/
def fixedPointsPermCongrEquiv (e : α ≃ β) (σ : Equiv.Perm α) :
    Function.fixedPoints σ ≃ Function.fixedPoints (e.permCongr σ) :=
  Equiv.subtypeEquiv e fun x => by
    change σ x = x ↔ e.permCongr σ (e x) = e x
    simp

/-- For an actual involution of a finite type, the total cardinality is the
number of fixed points plus twice the number of nontrivial cycles.  For an
involution, the entries of `cycleType` are all equal to two, so its length is
the number of two element orbits. -/
theorem card_eq_fixed_add_twice_cycleCount [DecidableEq α]
    (σ : Equiv.Perm α) (hσ : Function.Involutive σ) :
    Fintype.card α =
      Fintype.card (Function.fixedPoints σ) + 2 * σ.cycleType.card := by
  have hpow : σ ^ 2 = 1 := by
    ext x
    simpa [pow_two] using hσ x
  have hcycle :
      σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hfixed := Equiv.Perm.card_fixedPoints σ
  have hle := Equiv.Perm.sum_cycleType_le σ
  rw [hcycle] at hfixed hle
  simp only [Multiset.sum_replicate, Nat.nsmul_eq_mul] at hfixed hle
  omega

/-- Actual-involution form of the same recovery formula: the number of fixed
points is twice the number of orbits minus the total number of points. -/
theorem card_fixedPoints_eq_twice_orbitCount_sub_card [DecidableEq α]
    (σ : Equiv.Perm α) (hσ : Function.Involutive σ) :
    Fintype.card (Function.fixedPoints σ) =
      2 * (Fintype.card (Function.fixedPoints σ) + σ.cycleType.card) -
        Fintype.card α := by
  have hcard := card_eq_fixed_add_twice_cycleCount σ hσ
  omega

/-- Two involutions of the same finite type having the same number of fixed
points are conjugate.  The conjugating permutation is precisely an
equivariant equivalence of the corresponding `C₂`-sets. -/
theorem exists_equivariantPerm_of_fixed_card_eq [DecidableEq α]
    (σ τ : Equiv.Perm α) (hσ : Function.Involutive σ)
    (hτ : Function.Involutive τ)
    (hfixed : Fintype.card (Function.fixedPoints σ) =
      Fintype.card (Function.fixedPoints τ)) :
    ∃ f : Equiv.Perm α, ∀ x, f (σ x) = τ (f x) := by
  have hpowσ : σ ^ 2 = 1 := by
    ext x
    simpa [pow_two] using hσ x
  have hpowτ : τ ^ 2 = 1 := by
    ext x
    simpa [pow_two] using hτ x
  have hcycleσ :
      σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hpowσ
  have hcycleτ :
      τ.cycleType = Multiset.replicate τ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hpowτ
  have hcardσ := card_eq_fixed_add_twice_cycleCount σ hσ
  have hcardτ := card_eq_fixed_add_twice_cycleCount τ hτ
  have hcount : σ.cycleType.card = τ.cycleType.card := by omega
  have htype : σ.cycleType = τ.cycleType := by
    rw [hcycleσ, hcycleτ, hcount]
  obtain ⟨f, hf⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr htype)
  refine ⟨f, fun x => ?_⟩
  have hx := congrArg (fun p : Equiv.Perm α => p (f x)) hf
  simpa using hx

/-- Finite sets equipped with involutions are equivariantly equivalent when
their total cardinalities and their numbers of fixed points agree. -/
theorem exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
    [DecidableEq α] [DecidableEq β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (hcard : Fintype.card α = Fintype.card β)
    (hfixed : Fintype.card (Function.fixedPoints σ) =
      Fintype.card (Function.fixedPoints τ)) :
    ∃ f : α ≃ β, ∀ x, f (σ x) = τ (f x) := by
  let e : α ≃ β := Fintype.equivOfCardEq hcard
  have htransport : Function.Involutive (e.permCongr σ) := by
    intro y
    simp only [Equiv.permCongr_apply]
    simpa using congrArg e (hσ (e.symm y))
  have hfixedTransport :
      Fintype.card (Function.fixedPoints (e.permCongr σ)) =
        Fintype.card (Function.fixedPoints τ) := by
    rw [← Fintype.card_congr (fixedPointsPermCongrEquiv e σ)]
    exact hfixed
  obtain ⟨g, hg⟩ := exists_equivariantPerm_of_fixed_card_eq
    (e.permCongr σ) τ htransport hτ hfixedTransport
  refine ⟨e.trans g, fun x => ?_⟩
  change g (e (σ x)) = τ (g (e x))
  simpa using hg (e x)

end ActualFiniteInvolutions

/-- The orbit data of the disjoint union of a distinguished part and a
finite family of other parts. -/
def decompositionData {ι : Type*} [Fintype ι]
    (d₀ : C2OrbitData) (d : ι → C2OrbitData) : C2OrbitData :=
  d₀ + ∑ i, d i

/-- Cancellation for the decompositions in the manuscript: if the complete
unions have the same orbit data and all nondistinguished parts have matching
orbit data, then the remaining parts have matching orbit data. -/
theorem cancel_decomposition {ι : Type*} [Fintype ι]
    {d₀ e₀ : C2OrbitData} {d e : ι → C2OrbitData}
    (htotal : decompositionData d₀ d = decompositionData e₀ e)
    (hparts : ∀ i, d i = e i) : d₀ = e₀ := by
  have hsum : (∑ i, d i) = ∑ i, e i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hparts i
  simp only [decompositionData] at htotal
  rw [hsum] at htotal
  exact add_right_cancel htotal

/-- The involution on the standard model for two blocks exchanged by `C₂`. -/
def swapBlocks {α : Type*} : Sum α α → Sum α α
  | Sum.inl x => Sum.inr x
  | Sum.inr x => Sum.inl x

@[simp] theorem swapBlocks_involutive {α : Type*} (x : Sum α α) :
    swapBlocks (swapBlocks x) = x := by
  cases x <;> rfl

/-- A bijection chosen on one of two exchanged blocks, extended to their
union by using the same bijection on the other block. -/
def exchangedBlocksEquiv {α β : Type*} (f : α ≃ β) : Sum α α ≃ Sum β β :=
  Equiv.sumCongr f f

/-- The extended bijection commutes with the involutions exchanging the two
blocks. -/
theorem exchangedBlocksEquiv_equivariant {α β : Type*} (f : α ≃ β)
    (x : Sum α α) :
    exchangedBlocksEquiv f (swapBlocks x) =
      swapBlocks (exchangedBlocksEquiv f x) := by
  cases x <;> rfl

/-- The extended bijection sends each of the two blocks to the corresponding
block. -/
theorem exchangedBlocksEquiv_preserves_blocks {α β : Type*} (f : α ≃ β)
    (x : Sum α α) :
    (exchangedBlocksEquiv f x).isLeft = x.isLeft := by
  cases x <;> rfl

end Formalisation.C2Cancellation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
