import Formalisation.C2Cancellation

/-!
# The block cancellation lemma

This file gives a type-level version of the cancellation lemma used in the
sporadic section of the manuscript.  A finite `C₂`-set is represented by a
finite type and an involutive permutation.  A decomposition into invariant
parts is represented by a sum type, with the involution acting separately on
the two summands.

The main theorem `cancel_equivariant_equiv` says that an equivariant
equivalence between two complete decompositions, together with an equivariant
equivalence between the already matched parts, yields an equivariant
equivalence between the remaining parts.  The indexed version
`cancel_equivariant_equiv_of_parts` packages a finite family of already
matched parts into their disjoint union.

The final theorem formalises the block-preserving conclusion when the
remaining block orbit consists of two blocks exchanged by the involution.
From the cancellation hypotheses it derives that corresponding blocks have
equal cardinality, chooses a bijection on one block, and defines the map on
the other by applying the two involutions, exactly as in the manuscript.

The only residual gap between this file and the application in the manuscript
is representation theoretic: Lean does not establish that the character and
weight sets used there carry the asserted decompositions or that the cited
calculations provide the required equivalences on the known block parts.
-/

namespace Formalisation.BlockCancellation

/-- An equivalence intertwines two permutations. -/
def Intertwines {α β : Type*} (f : α ≃ β)
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) : Prop :=
  ∀ x, f (σ x) = τ (f x)

/-- The permutation acting separately on two invariant parts. -/
def sumPerm {α β : Type*} (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Equiv.Perm (Sum α β) :=
  Equiv.sumCongr σ τ

@[simp] theorem sumPerm_inl {α β : Type*} (σ : Equiv.Perm α)
    (τ : Equiv.Perm β) (x : α) :
    sumPerm σ τ (Sum.inl x) = Sum.inl (σ x) := rfl

@[simp] theorem sumPerm_inr {α β : Type*} (σ : Equiv.Perm α)
    (τ : Equiv.Perm β) (x : β) :
    sumPerm σ τ (Sum.inr x) = Sum.inr (τ x) := rfl

/-- An intertwining equivalence restricts to an equivalence of fixed point
sets. -/
def fixedPointsEquivOfIntertwines {α β : Type*} (f : α ≃ β)
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (hf : Intertwines f σ τ) :
  Function.fixedPoints σ ≃ Function.fixedPoints τ where
  toFun x := ⟨f x, by
    change τ (f x) = f x
    rw [← hf x, x.property]⟩
  invFun y := ⟨f.symm y, by
    apply f.injective
    rw [hf]
    simp only [Equiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact f.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact f.apply_symm_apply y

/-- The fixed points of the permutation on a disjoint union are the disjoint
union of the fixed points in its two invariant parts. -/
def fixedPointsSumEquiv {α β : Type*} (σ : Equiv.Perm α)
    (τ : Equiv.Perm β) :
    Function.fixedPoints (sumPerm σ τ) ≃
      Sum (Function.fixedPoints σ) (Function.fixedPoints τ) where
  toFun x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl a =>
        exact Sum.inl ⟨a, Sum.inl.inj hx⟩
    | inr b =>
        exact Sum.inr ⟨b, Sum.inr.inj hx⟩
  invFun x := by
    cases x with
    | inl a => exact ⟨Sum.inl a, congrArg Sum.inl a.property⟩
    | inr b => exact ⟨Sum.inr b, congrArg Sum.inr b.property⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x <;> rfl
  right_inv x := by
    cases x <;> rfl

/-- Fixed point counts add across a decomposition into two invariant parts. -/
theorem card_fixedPoints_sumPerm {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Fintype.card (Function.fixedPoints (sumPerm σ τ)) =
      Fintype.card (Function.fixedPoints σ) +
        Fintype.card (Function.fixedPoints τ) := by
  rw [Fintype.card_congr (fixedPointsSumEquiv σ τ)]
  exact Fintype.card_sum

/-- Exact cancellation for finite `C₂`-sets decomposed into a remaining
invariant part and the union of the already matched invariant parts. -/
theorem cancel_equivariant_equiv
    {Y₀ Y₁ Y₀' Y₁' : Type*}
    [Finite Y₀] [Finite Y₁] [Finite Y₀'] [Finite Y₁']
    (σ₀ : Equiv.Perm Y₀) (σ₁ : Equiv.Perm Y₁)
    (τ₀ : Equiv.Perm Y₀') (τ₁ : Equiv.Perm Y₁')
    (hσ₀ : Function.Involutive σ₀) (_hσ₁ : Function.Involutive σ₁)
    (hτ₀ : Function.Involutive τ₀) (_hτ₁ : Function.Involutive τ₁)
    (global : Sum Y₀ Y₁ ≃ Sum Y₀' Y₁')
    (hglobal : Intertwines global (sumPerm σ₀ σ₁) (sumPerm τ₀ τ₁))
    (known : Y₁ ≃ Y₁') (hknown : Intertwines known σ₁ τ₁) :
    ∃ remaining : Y₀ ≃ Y₀', Intertwines remaining σ₀ τ₀ := by
  classical
  let _ : Fintype Y₀ := Fintype.ofFinite Y₀
  let _ : Fintype Y₁ := Fintype.ofFinite Y₁
  let _ : Fintype Y₀' := Fintype.ofFinite Y₀'
  let _ : Fintype Y₁' := Fintype.ofFinite Y₁'
  have hglobalCard := Fintype.card_congr global
  have hknownCard := Fintype.card_congr known
  simp only [Fintype.card_sum] at hglobalCard
  have hremainingCard : Fintype.card Y₀ = Fintype.card Y₀' := by
    omega
  have hglobalFixed := Fintype.card_congr
    (fixedPointsEquivOfIntertwines global _ _ hglobal)
  have hknownFixed := Fintype.card_congr
    (fixedPointsEquivOfIntertwines known _ _ hknown)
  rw [card_fixedPoints_sumPerm, card_fixedPoints_sumPerm] at hglobalFixed
  have hremainingFixed :
      Fintype.card (Function.fixedPoints σ₀) =
        Fintype.card (Function.fixedPoints τ₀) := by
    omega
  exact C2Cancellation.exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
    σ₀ τ₀ hσ₀ hτ₀ hremainingCard hremainingFixed

/-- The permutation on a finite family of invariant parts. -/
def sigmaPerm {ι : Type*} {Y : ι → Type*}
    (σ : (i : ι) → Equiv.Perm (Y i)) : Equiv.Perm (Sigma Y) :=
  Equiv.sigmaCongrRight σ

@[simp] theorem sigmaPerm_apply {ι : Type*} {Y : ι → Type*}
    (σ : (i : ι) → Equiv.Perm (Y i)) (x : Sigma Y) :
    sigmaPerm σ x = ⟨x.1, σ x.1 x.2⟩ := rfl

/-- Equivariant equivalences on every part combine to an equivariant
equivalence on their disjoint union. -/
theorem sigmaCongrRight_intertwines
    {ι : Type*} {Y Y' : ι → Type*}
    (σ : (i : ι) → Equiv.Perm (Y i))
    (τ : (i : ι) → Equiv.Perm (Y' i))
    (f : (i : ι) → Y i ≃ Y' i)
    (hf : ∀ i, Intertwines (f i) (σ i) (τ i)) :
    Intertwines (Equiv.sigmaCongrRight f) (sigmaPerm σ) (sigmaPerm τ) := by
  rintro ⟨i, x⟩
  change (⟨i, f i (σ i x)⟩ : Sigma Y') = ⟨i, τ i (f i x)⟩
  congr 1
  exact hf i x

/-- Indexed form of `cancel_equivariant_equiv`, matching the manuscript's
decompositions into a distinguished part and finitely many known parts. -/
theorem cancel_equivariant_equiv_of_parts
    {ι : Type*} {Y₀ Y₀' : Type*} {Y Y' : ι → Type*}
    [Finite ι] [Finite Y₀] [Finite Y₀']
    [∀ i, Finite (Y i)] [∀ i, Finite (Y' i)]
    (σ₀ : Equiv.Perm Y₀) (τ₀ : Equiv.Perm Y₀')
    (σ : (i : ι) → Equiv.Perm (Y i))
    (τ : (i : ι) → Equiv.Perm (Y' i))
    (hσ₀ : Function.Involutive σ₀)
    (hσ : ∀ i, Function.Involutive (σ i))
    (hτ₀ : Function.Involutive τ₀)
    (hτ : ∀ i, Function.Involutive (τ i))
    (global : Sum Y₀ (Sigma Y) ≃ Sum Y₀' (Sigma Y'))
    (hglobal : Intertwines global (sumPerm σ₀ (sigmaPerm σ))
      (sumPerm τ₀ (sigmaPerm τ)))
    (known : (i : ι) → Y i ≃ Y' i)
    (hknown : ∀ i, Intertwines (known i) (σ i) (τ i)) :
    ∃ remaining : Y₀ ≃ Y₀', Intertwines remaining σ₀ τ₀ := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype Y₀ := Fintype.ofFinite Y₀
  let _ : Fintype Y₀' := Fintype.ofFinite Y₀'
  let _ (i : ι) : Fintype (Y i) := Fintype.ofFinite (Y i)
  let _ (i : ι) : Fintype (Y' i) := Fintype.ofFinite (Y' i)
  have hSigmaσ : Function.Involutive (sigmaPerm σ) := by
    rintro ⟨i, x⟩
    change (⟨i, σ i (σ i x)⟩ : Sigma Y) = ⟨i, x⟩
    congr 1
    exact hσ i x
  have hSigmaτ : Function.Involutive (sigmaPerm τ) := by
    rintro ⟨i, x⟩
    change (⟨i, τ i (τ i x)⟩ : Sigma Y') = ⟨i, x⟩
    congr 1
    exact hτ i x
  exact cancel_equivariant_equiv σ₀ (sigmaPerm σ) τ₀ (sigmaPerm τ)
    hσ₀ hSigmaσ hτ₀ hSigmaτ global hglobal
    (Equiv.sigmaCongrRight known)
    (sigmaCongrRight_intertwines σ τ known hknown)

section ExchangedBlocks

variable {Y₀ Y₁ Y₀' Y₁' : Type*}

/-- An involution exchanging two blocks, described by mutually inverse
bijections between their underlying sets. -/
def exchangedPerm (s : Y₀ ≃ Y₁) : Equiv.Perm (Sum Y₀ Y₁) where
  toFun
    | Sum.inl x => Sum.inr (s x)
    | Sum.inr y => Sum.inl (s.symm y)
  invFun
    | Sum.inl x => Sum.inr (s x)
    | Sum.inr y => Sum.inl (s.symm y)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

@[simp] theorem exchangedPerm_inl (s : Y₀ ≃ Y₁) (x : Y₀) :
    exchangedPerm s (Sum.inl x) = Sum.inr (s x) := rfl

@[simp] theorem exchangedPerm_inr (s : Y₀ ≃ Y₁) (y : Y₁) :
    exchangedPerm s (Sum.inr y) = Sum.inl (s.symm y) := rfl

/-- The permutation exchanging the two blocks is an involution. -/
theorem exchangedPerm_involutive (s : Y₀ ≃ Y₁) :
    Function.Involutive (exchangedPerm s) := by
  rintro (x | y) <;> simp

/-- Given a bijection on one of two exchanged blocks, the map on the other
block is forced by equivariance: apply the source involution, the chosen
bijection, and then the target involution. -/
def exchangedBlockOrbitEquiv (s : Y₀ ≃ Y₁) (t : Y₀' ≃ Y₁')
    (f : Y₀ ≃ Y₀') : Sum Y₀ Y₁ ≃ Sum Y₀' Y₁' :=
  Equiv.sumCongr f (s.symm.trans (f.trans t))

/-- The extension from one block intertwines the involutions exchanging the
two blocks. -/
theorem exchangedBlockOrbitEquiv_intertwines
    (s : Y₀ ≃ Y₁) (t : Y₀' ≃ Y₁') (f : Y₀ ≃ Y₀') :
    Intertwines (exchangedBlockOrbitEquiv s t f)
      (exchangedPerm s) (exchangedPerm t) := by
  rintro (x | y) <;> simp [exchangedBlockOrbitEquiv]

/-- The extension preserves the two block labels: the first source block maps
to the first target block and the second source block maps to the second
target block. -/
theorem exchangedBlockOrbitEquiv_preserves_blocks
    (s : Y₀ ≃ Y₁) (t : Y₀' ≃ Y₁') (f : Y₀ ≃ Y₀') (x : Sum Y₀ Y₁) :
    (exchangedBlockOrbitEquiv s t f x).isLeft = x.isLeft := by
  cases x <;> rfl

/-- Block-preserving cancellation when the remaining block orbit consists of
two blocks exchanged by the involution.  Unlike
`exchangedBlockOrbitEquiv`, this theorem does not assume a bijection on one
block.  Its existence follows from the global equivalence after cancellation
of the known invariant parts. -/
theorem cancel_exchanged_blocks_preserving
    {K K' : Type*}
    [Finite Y₀] [Finite Y₁] [Finite Y₀'] [Finite Y₁']
    [Finite K] [Finite K']
    (s : Y₀ ≃ Y₁) (t : Y₀' ≃ Y₁')
    (κ : Equiv.Perm K) (κ' : Equiv.Perm K')
    (hκ : Function.Involutive κ) (hκ' : Function.Involutive κ')
    (global : Sum (Sum Y₀ Y₁) K ≃ Sum (Sum Y₀' Y₁') K')
    (hglobal : Intertwines global
      (sumPerm (exchangedPerm s) κ)
      (sumPerm (exchangedPerm t) κ'))
    (known : K ≃ K') (hknown : Intertwines known κ κ') :
    ∃ remaining : Sum Y₀ Y₁ ≃ Sum Y₀' Y₁',
      Intertwines remaining (exchangedPerm s) (exchangedPerm t) ∧
        ∀ x, (remaining x).isLeft = x.isLeft := by
  classical
  let _ : Fintype Y₀ := Fintype.ofFinite Y₀
  let _ : Fintype Y₁ := Fintype.ofFinite Y₁
  let _ : Fintype Y₀' := Fintype.ofFinite Y₀'
  let _ : Fintype Y₁' := Fintype.ofFinite Y₁'
  obtain ⟨remaining, _hremaining⟩ := cancel_equivariant_equiv
    (exchangedPerm s) κ (exchangedPerm t) κ'
    (exchangedPerm_involutive s) hκ
    (exchangedPerm_involutive t) hκ'
    global hglobal known hknown
  have hpairCard := Fintype.card_congr remaining
  have hsCard := Fintype.card_congr s
  have htCard := Fintype.card_congr t
  simp only [Fintype.card_sum] at hpairCard
  have hfirstCard : Fintype.card Y₀ = Fintype.card Y₀' := by
    omega
  let first : Y₀ ≃ Y₀' := Fintype.equivOfCardEq hfirstCard
  exact ⟨exchangedBlockOrbitEquiv s t first,
    exchangedBlockOrbitEquiv_intertwines s t first,
    exchangedBlockOrbitEquiv_preserves_blocks s t first⟩

end ExchangedBlocks

end Formalisation.BlockCancellation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
