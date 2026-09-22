import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers

/-!
# One-component rational forms on literal fixed-point carriers

This file performs the group-theoretic restriction following an explicitly
given geometric component embedding and its Steinberg square. The geometric
root datum, field parameter, graph action, simple connectedness, pinning and
classical-model interpretation remain external standard source boundaries.

The displayed Lang equation is the one-way instance of Lang--Steinberg
needed here (Malle--Testerman, Theorem 21.7, p. 184). Classification up to the
displayed inner twist belongs to Theorem 22.5, p. 191. Neither result is
replaced by a finite-factor equivalence or a rank-three inventory input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsRationalForms

open TypeBRegularLeviRationalCarriers

variable {S B R : Type*} [Group S] [Group B] [Group R]

/-- Adjust the same geometric embedding by the displayed conjugating element. -/
def adjustedEmbedding (j : S →* B) (a : S) : S →* B where
  toFun x := j (a * x * a⁻¹)
  map_one' := by simp
  map_mul' x y := by simp [map_mul, mul_assoc]

@[simp] theorem adjustedEmbedding_value (j : S →* B) (a x : S) :
    adjustedEmbedding j a x = j (a * x * a⁻¹) := rfl

theorem adjustedEmbedding_injective (j : S →* B)
    (j_injective : Function.Injective j) (a : S) :
    Function.Injective (adjustedEmbedding j a) := by
  intro x y h
  have hconj : a * x * a⁻¹ = a * y * a⁻¹ := j_injective h
  have hcancel := congrArg (fun z : S ↦ a⁻¹ * z * a) hconj
  simpa [mul_assoc] using hcancel

theorem adjustedEmbedding_range (j : S →* B) (H : Subgroup B)
    (j_range : j.range = H) (a : S) :
    (adjustedEmbedding j a).range = H := by
  apply le_antisymm
  · rintro b ⟨x, rfl⟩
    rw [← j_range]
    exact ⟨a * x * a⁻¹, rfl⟩
  · intro b hb
    have hb_range : b ∈ j.range := by rw [j_range]; exact hb
    obtain ⟨x, rfl⟩ := hb_range
    refine ⟨a⁻¹ * x * a, ?_⟩
    simp [adjustedEmbedding, mul_assoc]

/-- The Lang equation removes the displayed inner twist with this orientation. -/
theorem adjustedEmbedding_frobenius (j : S →* B) (Ψ : B →* B)
    (Φ : S →* S) (c : S)
    (return_value : ∀ x, Ψ (j x) = j (c * Φ x * c⁻¹))
    (a : S) (lang_value : Φ a * a⁻¹ = c⁻¹) (x : S) :
    Ψ (adjustedEmbedding j a x) = adjustedEmbedding j a (Φ x) := by
  have hca : c * Φ a = a := by
    have h := congrArg (fun z : S ↦ c * z * a) lang_value
    simpa [mul_assoc] using h
  change Ψ (j (a * x * a⁻¹)) = j (a * Φ x * a⁻¹)
  rw [return_value]
  apply congrArg j
  calc
    c * Φ (a * x * a⁻¹) * c⁻¹ =
        (c * Φ a) * Φ x * (c * Φ a)⁻¹ := by
      simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
    _ = a * Φ x * a⁻¹ := by rw [hca]

/-- Restrict commuting literal maps to the actual ambient fixed subgroup. -/
def finiteToRational (l : S →* B) (H : Subgroup B)
    (l_range : l.range = H) (Ψ : B →* B) (Φ : S →* S)
    (commutes : ∀ x, Ψ (l x) = l (Φ x))
    (i : R →* S) (i_range : i.range = fixedPoints Φ) :
    R →* rationalSubgroup Ψ H where
  toFun r := by
    have hi : i r ∈ fixedPoints Φ := by
      rw [← i_range]
      exact ⟨r, rfl⟩
    have hfixed : Φ (i r) = i r := hi
    exact ⟨⟨l (i r), (commutes (i r)).trans (congrArg l hfixed)⟩,
      by rw [← l_range]; exact ⟨i r, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext ((l.comp i).map_one))
  map_mul' r s := Subtype.ext (Subtype.ext ((l.comp i).map_mul r s))

@[simp] theorem finiteToRational_value (l : S →* B) (H : Subgroup B)
    (l_range : l.range = H) (Ψ : B →* B) (Φ : S →* S)
    (commutes : ∀ x, Ψ (l x) = l (Φ x))
    (i : R →* S) (i_range : i.range = fixedPoints Φ) (r : R) :
    (finiteToRational l H l_range Ψ Φ commutes i i_range r).1.1 = l (i r) := rfl

theorem finiteToRational_bijective (l : S →* B) (H : Subgroup B)
    (l_injective : Function.Injective l) (l_range : l.range = H)
    (Ψ : B →* B) (Φ : S →* S)
    (commutes : ∀ x, Ψ (l x) = l (Φ x))
    (i : R →* S) (i_injective : Function.Injective i)
    (i_range : i.range = fixedPoints Φ) :
    Function.Bijective (finiteToRational l H l_range Ψ Φ commutes i i_range) := by
  constructor
  · intro r s h
    apply i_injective
    apply l_injective
    exact congrArg (fun z : rationalSubgroup Ψ H ↦ z.1.1) h
  · intro y
    have hy_range : y.1.1 ∈ l.range := by rw [l_range]; exact y.2
    obtain ⟨x, hx⟩ := hy_range
    have hx_fixed : Φ x = x := by
      apply l_injective
      calc
        l (Φ x) = Ψ (l x) := (commutes x).symm
        _ = Ψ y.1.1 := congrArg Ψ hx
        _ = y.1.1 := y.1.2
        _ = l x := hx.symm
    have hx_range : x ∈ i.range := by rw [i_range]; exact hx_fixed
    obtain ⟨r, hr⟩ := hx_range
    refine ⟨r, Subtype.ext (Subtype.ext ?_)⟩
    change l (i r) = y.1.1
    exact (congrArg l hr).trans hx

/-- The finite equivalence is constructed from the two literal range statements. -/
def finiteRationalEquiv (l : S →* B) (H : Subgroup B)
    (l_injective : Function.Injective l) (l_range : l.range = H)
    (Ψ : B →* B) (Φ : S →* S)
    (commutes : ∀ x, Ψ (l x) = l (Φ x))
    (i : R →* S) (i_injective : Function.Injective i)
    (i_range : i.range = fixedPoints Φ) :
    R ≃* rationalSubgroup Ψ H :=
  MulEquiv.ofBijective (finiteToRational l H l_range Ψ Φ commutes i i_range)
    (finiteToRational_bijective l H l_injective l_range Ψ Φ commutes
      i i_injective i_range)

@[simp] theorem finiteRationalEquiv_value (l : S →* B) (H : Subgroup B)
    (l_injective : Function.Injective l) (l_range : l.range = H)
    (Ψ : B →* B) (Φ : S →* S)
    (commutes : ∀ x, Ψ (l x) = l (Φ x))
    (i : R →* S) (i_injective : Function.Injective i)
    (i_range : i.range = fixedPoints Φ) (r : R) :
    (finiteRationalEquiv l H l_injective l_range Ψ Φ commutes
      i i_injective i_range r).1.1 = l (i r) := rfl

theorem finiteRationalEquiv_symm_value (l : S →* B) (H : Subgroup B)
    (l_injective : Function.Injective l) (l_range : l.range = H)
    (Ψ : B →* B) (Φ : S →* S)
    (commutes : ∀ x, Ψ (l x) = l (Φ x))
    (i : R →* S) (i_injective : Function.Injective i)
    (i_range : i.range = fixedPoints Φ) (y : rationalSubgroup Ψ H) :
    l (i ((finiteRationalEquiv l H l_injective l_range Ψ Φ commutes
      i i_injective i_range).symm y)) = y.1.1 := by
  exact congrArg (fun z : rationalSubgroup Ψ H ↦ z.1.1)
    ((finiteRationalEquiv l H l_injective l_range Ψ Φ commutes
      i i_injective i_range).apply_symm_apply y)

/-- A narrow Lang instance yields the same adjusted embedding, its square,
and the constructed rational-form equivalence with both ambient value laws. -/
theorem exists_rationalForm (j : S →* B) (H : Subgroup B)
    (j_injective : Function.Injective j) (j_range : j.range = H)
    (Ψ : B →* B) (Φ : S →* S) (c : S)
    (return_value : ∀ x, Ψ (j x) = j (c * Φ x * c⁻¹))
    (lang : ∃ a : S, Φ a * a⁻¹ = c⁻¹)
    (i : R →* S) (i_injective : Function.Injective i)
    (i_range : i.range = fixedPoints Φ) :
    ∃ a : S, Φ a * a⁻¹ = c⁻¹ ∧
      (∀ x, Ψ (adjustedEmbedding j a x) = adjustedEmbedding j a (Φ x)) ∧
      ∃ e : R ≃* rationalSubgroup Ψ H,
        (∀ r, (e r).1.1 = j (a * i r * a⁻¹)) ∧
        (∀ y, j (a * i (e.symm y) * a⁻¹) = y.1.1) := by
  obtain ⟨a, ha⟩ := lang
  have hinj := adjustedEmbedding_injective j j_injective a
  have hrange := adjustedEmbedding_range j H j_range a
  have square := adjustedEmbedding_frobenius j Ψ Φ c return_value a ha
  let e := finiteRationalEquiv (adjustedEmbedding j a) H hinj hrange
    Ψ Φ square i i_injective i_range
  refine ⟨a, ha, square, e, ?_, ?_⟩
  · intro r
    rfl
  · intro y
    exact finiteRationalEquiv_symm_value (adjustedEmbedding j a) H hinj hrange
      Ψ Φ square i i_injective i_range y

end ModularRep.PaperProofs.TypeBRankThreeFactorsRationalForms


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
