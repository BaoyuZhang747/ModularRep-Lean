import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
The two invariant subset deductions in the Fi24′ proof at two.
-/

noncomputable section

namespace ManuscriptIBAW.Sporadic.Fi24TwoCounting

variable {α : Type*} [DecidableEq α]

def fixed (f : α → α) (s : Finset α) : Finset α :=
  s.filter (fun x => f x = x)

def Stable (f : α → α) (s : Finset α) : Prop :=
  ∀ x, x ∈ s → f x ∈ s

theorem fixed_sdiff (f : α → α) (s t : Finset α) :
    fixed f (s \ t) = fixed f s \ fixed f t := by
  classical
  ext x
  simp only [fixed, Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem fixed_mono (f : α → α) {s t : Finset α} (h : s ⊆ t) :
    fixed f s ⊆ fixed f t := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hx).1,
    (Finset.mem_filter.mp hx).2⟩

theorem stable_sdiff (f : α → α) (hf : Function.Involutive f)
    {s t : Finset α} (hs : Stable f s) (ht : Stable f t) :
    Stable f (s \ t) := by
  intro x hx
  obtain ⟨hxs, hxt⟩ := Finset.mem_sdiff.mp hx
  refine Finset.mem_sdiff.mpr ⟨hs x hxs, ?_⟩
  intro hft
  have := ht (f x) hft
  exact hxt (by simpa only [hf x] using this)

theorem singleton_stable_fixed (f : α → α) {s : Finset α}
    (hs : Stable f s) (hcard : s.card = 1) : fixed f s = s := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  have hx : f x = x := Finset.mem_singleton.mp (hs x (Finset.mem_singleton_self x))
  ext y
  simp only [fixed, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro hy
    exact ⟨hy, by simpa only [hy] using hx⟩

/-- An invariant subset of size three in a set of size four with two fixed
points has exactly one fixed point. No allocation of individual points is
supplied. -/
theorem three_in_four (f : α → α) (hf : Function.Involutive f)
    {s row : Finset α} (hs : Stable f s) (hr : Stable f row)
    (hsub : s ⊆ row) (hrow : row.card = 4) (hfix : (fixed f row).card = 2)
    (hthree : s.card = 3) : (fixed f s).card = 1 := by
  have hcompl : (row \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hrow, hthree]
  have hcomplfix := singleton_stable_fixed f (stable_sdiff f hf hr hs) hcompl
  have hcount : (fixed f row).card - (fixed f s).card = 1 := by
    rw [← Finset.card_sdiff_of_subset (fixed_mono f hsub), ← fixed_sdiff, hcomplfix, hcompl]
  have hle : (fixed f s).card ≤ (fixed f row).card :=
    Finset.card_le_card (fixed_mono f hsub)
  omega

/-- The second block has three weights and exhausts the complement among the six
possible weights. All three are fixed. -/
theorem remaining_three (f : α → α) {s t possible : Finset α}
    (hsub : s ⊆ possible) (ht : t ⊆ possible \ s)
    (hpossible : possible.card = 6) (hfixed : (fixed f possible).card = 4)
    (hs : s.card = 3) (hsfixed : (fixed f s).card = 1)
    (htcard : t.card = 3) :
    t = possible \ s ∧ (fixed f t).card = 3 := by
  have hc : (possible \ s).card = 3 := by
    rw [Finset.card_sdiff_of_subset hsub, hpossible, hs]
  have heq : t = possible \ s := Finset.eq_of_subset_of_card_le ht (by omega)
  refine ⟨heq, ?_⟩
  rw [heq, fixed_sdiff, Finset.card_sdiff_of_subset (fixed_mono f hsub), hfixed, hsfixed]

def support (P : α → Prop) [Finite {x // P x}] : Finset α :=
  letI := Fintype.ofFinite {x // P x}
  (Finset.univ : Finset {x // P x}).map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_support (P : α → Prop) [Finite {x // P x}] (x : α) :
    x ∈ support P ↔ P x := by
  classical
  simp [support]

theorem card_support (P : α → Prop) [Finite {x // P x}] :
    (support P).card = Nat.card {x // P x} := by
  let := Fintype.ofFinite {x // P x}
  simp [support, Nat.card_eq_fintype_card]

theorem card_fixed_support (f : α → α) (P : α → Prop) [Finite {x // P x}] :
    (fixed f (support P)).card = Nat.card {x // P x ∧ f x = x} := by
  have : Finite {x // P x ∧ f x = x} :=
    Finite.of_injective (fun x : {x // P x ∧ f x = x} => (⟨x.1, x.2.1⟩ : {x // P x}))
      (fun _ _ h => Subtype.ext (congrArg (fun x : {x // P x} => x.1) h))
  have heq : fixed f (support P) = support (fun x => P x ∧ f x = x) := by
    ext x
    simp only [fixed, Finset.mem_filter, mem_support]
  rw [heq, card_support]

/-- The ambient set need not be finite. Each of the four subsets is finite
because its given natural cardinality is nonzero. -/
theorem predicate_counts (f : α → α) (hf : Function.Involutive f)
    (P Q row possible : α → Prop)
    (hPstable : ∀ x, P x → P (f x)) (hrstable : ∀ x, row x → row (f x))
    (hPr : ∀ x, P x → row x) (hrU : ∀ x, row x → possible x)
    (hQU : ∀ x, Q x → possible x) (hdisjoint : ∀ x, Q x → ¬ P x)
    (hP : Nat.card {x // P x} = 3) (hQ : Nat.card {x // Q x} = 3)
    (hr : Nat.card {x // row x} = 4)
    (hrf : Nat.card {x // row x ∧ f x = x} = 2)
    (hU : Nat.card {x // possible x} = 6)
    (hUf : Nat.card {x // possible x ∧ f x = x} = 4) :
    Nat.card {x // P x ∧ f x = x} = 1 ∧
      Nat.card {x // Q x ∧ f x = x} = 3 := by
  let : Finite {x // P x} := Nat.finite_of_card_ne_zero (by omega)
  let : Finite {x // Q x} := Nat.finite_of_card_ne_zero (by omega)
  let : Finite {x // row x} := Nat.finite_of_card_ne_zero (by omega)
  let : Finite {x // possible x} := Nat.finite_of_card_ne_zero (by omega)
  have hsub : support P ⊆ support row := by simpa only [Finset.subset_iff, mem_support] using hPr
  have hfirst := three_in_four f hf (s := support P) (row := support row)
    (by simpa only [Stable, mem_support] using hPstable)
    (by simpa only [Stable, mem_support] using hrstable) hsub
    (by rwa [card_support]) (by rwa [card_fixed_support]) (by rwa [card_support])
  have hsecond := remaining_three f (s := support P) (t := support Q)
    (possible := support possible)
    (by simpa only [Finset.subset_iff, mem_support] using fun x hx => hrU x (hPr x hx))
    (by simpa only [Finset.subset_iff, Finset.mem_sdiff, mem_support] using
      fun x hx => And.intro (hQU x hx) (hdisjoint x hx))
    (by rwa [card_support]) (by rwa [card_fixed_support])
    (by rwa [card_support]) hfirst (by rwa [card_support])
  exact ⟨by simpa only [card_fixed_support] using hfirst,
    by simpa only [card_fixed_support] using hsecond.2⟩

theorem card_or (P Q : α → Prop) [Finite {x // P x}] [Finite {x // Q x}]
    (hd : ∀ x, P x → Q x → False) :
    Nat.card {x // P x ∨ Q x} = Nat.card {x // P x} + Nat.card {x // Q x} := by
  classical
  have hdis : Disjoint P Q := disjoint_iff_inf_le.mpr (fun x hx => hd x hx.1 hx.2)
  exact (Nat.card_congr (subtypeOrEquiv P Q hdis)).trans Nat.card_sum

theorem card_three_rows (P Q S : α → Prop)
    [Finite {x // P x}] [Finite {x // Q x}] [Finite {x // S x}]
    (hPQ : ∀ x, P x → Q x → False) (hPS : ∀ x, P x → S x → False)
    (hQS : ∀ x, Q x → S x → False) :
    Nat.card {x // P x ∨ Q x ∨ S x} =
      Nat.card {x // P x} + Nat.card {x // Q x} + Nat.card {x // S x} := by
  classical
  have hdis : Disjoint Q S := disjoint_iff_inf_le.mpr (fun x hx => hQS x hx.1 hx.2)
  have : Finite {x // Q x ∨ S x} :=
    (subtypeOrEquiv Q S hdis).finite_iff.mpr inferInstance
  rw [card_or P (fun x => Q x ∨ S x) (fun x hp h => h.elim (hPQ x hp) (hPS x hp)),
    card_or Q S hQS, Nat.add_assoc]

end ManuscriptIBAW.Sporadic.Fi24TwoCounting

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
