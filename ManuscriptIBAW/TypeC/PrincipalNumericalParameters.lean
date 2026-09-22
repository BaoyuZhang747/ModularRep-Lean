import ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource

/-!
# The numerical parameters for x − 1 in Feng–Malle

Proposition 5.4 assigns a staircase to each local colour of rank `2^d`.
There are three colours at `d=0` and `2^(d+1)` at positive `d`.
Lemma 5.1 fixes one colour and interchanges two at `d=0`. At positive
`d` it fixes `2^d` colours and interchanges `2^(d-1)` pairs. We use a
disjoint sum to display these fixed and interchanged colours explicitly.

Only indices `d≤n` are needed for rank `n`. The omitted positive entries
would already contribute more than `n` to the weighted rank sum.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource

def fmFixedColours (d : ℕ) : ℕ := if d = 0 then 1 else 2 ^ d
def fmColourPairs (d : ℕ) : ℕ := if d = 0 then 1 else 2 ^ (d - 1)

abbrev FMColour (d : ℕ) :=
  Fin (fmFixedColours d) ⊕ (Fin (fmColourPairs d) × Bool)

theorem fmColour_card_zero : Fintype.card (FMColour 0) = 3 := by decide

theorem fmColour_card_positive (d : ℕ) (hd : 0 < d) :
    Fintype.card (FMColour d) = 2 ^ (d + 1) := by
  have he : 2 ^ d = 2 ^ (d - 1) * 2 := by
    conv_lhs => rw [show d = d - 1 + 1 by omega]
    rw [pow_succ]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool, fmFixedColours, fmColourPairs, if_neg (Nat.ne_of_gt hd)]
  rw [← he, pow_succ]
  omega

def fmColourDiagonal (d : ℕ) : FMColour d ≃ FMColour d where
  toFun
    | .inl c => .inl c
    | .inr (c, b) => .inr (c, !b)
  invFun
    | .inl c => .inl c
    | .inr (c, b) => .inr (c, !b)
  left_inv c := by cases c with
    | inl c => rfl
    | inr c => rcases c with ⟨c, b⟩; cases b <;> rfl
  right_inv c := by cases c with
    | inl c => rfl
    | inr c => rcases c with ⟨c, b⟩; cases b <;> rfl

abbrev FMPalette (n : ℕ) := Σ d : Fin (n + 1), FMColour d.1

def fmPaletteDiagonal (n : ℕ) : FMPalette n ≃ FMPalette n :=
  Equiv.sigmaCongrRight (fun d => fmColourDiagonal d.1)

theorem fmPaletteDiagonal_involutive (n : ℕ) :
    Function.Involutive (fmPaletteDiagonal n) := by
  rintro ⟨d, c⟩
  cases c with
  | inl c => rfl
  | inr c => rcases c with ⟨c, b⟩; cases b <;> rfl

def fmRank {n : ℕ} (height : FMPalette n → ℕ) : ℕ :=
  ∑ c, 2 ^ c.1.1 * triangular (height c)

/-- The precise staircase size condition of FM Proposition 5.4. -/
def FMParameter (n : ℕ) := {height : FMPalette n → ℕ // fmRank height = n}

theorem fmParameter_height_le {n : ℕ} (h : FMParameter n) (c : FMPalette n) :
    h.1 c ≤ n := by
  have hweight : 1 ≤ 2 ^ c.1.1 := Nat.one_le_pow _ _ (by omega)
  have hs : 2 ^ c.1.1 * triangular (h.1 c) ≤ n := by
    calc
      _ ≤ fmRank h.1 :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      _ = n := h.2
  have ht := height_le_triangular (h.1 c)
  nlinarith

instance fmParameter_finite (n : ℕ) : Finite (FMParameter n) := by
  let f : FMParameter n → (FMPalette n → Fin (n + 1)) :=
    fun h c => ⟨h.1 c, Nat.lt_succ_of_le (fmParameter_height_le h c)⟩
  apply Finite.of_injective f
  intro h k heq
  apply Subtype.ext
  funext c
  exact congrArg Fin.val (congrFun heq c)

theorem fmRank_diagonal {n : ℕ} (h : FMPalette n → ℕ) :
    fmRank (fun c => h (fmPaletteDiagonal n c)) = fmRank h := by
  unfold fmRank
  exact Equiv.sum_comp (fmPaletteDiagonal n)
    (fun c => 2 ^ c.1.1 * triangular (h c))

def fmParameterDiagonal (n : ℕ) : FMParameter n ≃ FMParameter n where
  toFun h := ⟨fun c => h.1 (fmPaletteDiagonal n c), (fmRank_diagonal h.1).trans h.2⟩
  invFun h := ⟨fun c => h.1 (fmPaletteDiagonal n c), (fmRank_diagonal h.1).trans h.2⟩
  left_inv h := by
    apply Subtype.ext
    funext c
    exact congrArg h.1 (fmPaletteDiagonal_involutive n c)
  right_inv h := by
    apply Subtype.ext
    funext c
    exact congrArg h.1 (fmPaletteDiagonal_involutive n c)

theorem fmParameterDiagonal_involutive (n : ℕ) :
    Function.Involutive (fmParameterDiagonal n) := by
  intro h
  exact (fmParameterDiagonal n).left_inv h

/-- The colour set in all ranks, before truncating Feng–Malle's condition. -/
abbrev FMUnboundedPalette := Σ d : ℕ, FMColour d

def fmUnboundedRank (height : FMUnboundedPalette →₀ ℕ) : ℕ :=
  height.sum (fun c h => 2 ^ c.1 * triangular h)

def FMUnboundedParameter (n : ℕ) :=
  {height : FMUnboundedPalette →₀ ℕ // fmUnboundedRank height = n}

/-- Every nonzero staircase contributes its full weighted size to the
finite rank sum in FM Proposition 5.4. -/
theorem fmUnboundedParameter_contribution_le {n : ℕ} (h : FMUnboundedParameter n)
    (c : FMUnboundedPalette) : 2 ^ c.1 * triangular (h.1 c) ≤ n := by
  classical
  by_cases hc : h.1 c = 0
  · simp [hc, triangular]
  · have hmem : c ∈ h.1.support := Finsupp.mem_support_iff.mpr hc
    calc
      _ ≤ fmUnboundedRank h.1 :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      _ = n := h.2

/-- A colour above the truncation bound has height zero. Thus the finite colour
set omits no assignment of total rank `n` from the printed condition. -/
theorem fmUnboundedParameter_height_zero_of_rank_gt {n : ℕ}
    (h : FMUnboundedParameter n) (d : ℕ) (hd : n < d) (c : FMColour d) :
    h.1 ⟨d, c⟩ = 0 := by
  have hs := fmUnboundedParameter_contribution_le h ⟨d, c⟩
  have hp := d.lt_two_pow_self
  have ht := height_le_triangular (h.1 ⟨d, c⟩)
  by_contra hzero
  have hh : 1 ≤ h.1 ⟨d, c⟩ := Nat.one_le_iff_ne_zero.mpr hzero
  nlinarith

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
