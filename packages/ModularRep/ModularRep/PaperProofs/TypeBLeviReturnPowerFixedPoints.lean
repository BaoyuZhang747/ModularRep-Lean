import ModularRep.PaperProofs.TypeBRankThreeFactorsRationalForms

/-!
# Simultaneous return powers on the same Levi component

Powers below are powers in Monoid.End, hence composition powers. If the
arithmetic correction has k ≤ 0, take q = (-k).toNat and v = a * t.
The two natural equalities are supplied by the separate component-period
arithmetic; no inverse of a geometric Frobenius is required here.

Only the single map F0 ^ u must preserve the displayed component subgroup.
Its two powers give the corrected return and the defining fixed-point map.
A single normalized generator square propagates to both powers, on the same
adjusted embedding. The original coordinate-return square remains literal.

The algebraic-group interpretation of that generator, its field parameter,
graph action and pinning are external standard boundaries. Lang--Steinberg
(Malle--Testerman, Theorem 21.7, p. 184) supplies the single displayed Lang
equation after the standard inner-twist classification (Theorem 22.5, p. 191).
This group deduction supplies no classification or Lang source inhabitant.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnPowerFixedPoints

open TypeBRegularLeviRationalCarriers
open TypeBRankThreeFactorsRationalForms

variable {B S : Type*} [Group B] [Group S]

/-- The corrected return is a power of the same component Frobenius. -/
theorem corrected_power (F0 F : Monoid.End B) (h u v q r : ℕ)
    (hF : F = F0 ^ h) (exponent : v + h * q = u * r) :
    (F ^ q).comp (F0 ^ v) = (F0 ^ u) ^ r := by
  change F ^ q * F0 ^ v = (F0 ^ u) ^ r
  simp only [hF, ← pow_mul, ← pow_add]
  rw [Nat.add_comm (h * q) v, exponent]

/-- The defining Frobenius is another power of that same map. -/
theorem defining_power (F0 F : Monoid.End B) (h u d s : ℕ)
    (hF : F = F0 ^ h) (exponent : h * d = u * s) :
    F ^ d = (F0 ^ u) ^ s := by
  simp only [hF, ← pow_mul]
  rw [exponent]

/-- Intertwining one generator intertwines each of its composition powers. -/
theorem intertwining_power (j : S →* B) (Ψ : Monoid.End B) (Φ : Monoid.End S)
    (square : ∀ x, Ψ (j x) = j (Φ x)) (n : ℕ) (x : S) :
    (Ψ ^ n) (j x) = j ((Φ ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ']
      change Ψ ((Ψ ^ n) (j x)) = j (Φ ((Φ ^ n) x))
      rw [ih, square]

/-- Restrict only the common component Frobenius, keeping composition powers. -/
abbrev componentEnd (T : Monoid.End B) (U : Subgroup B)
    (stable : ∀ x ∈ U, T x ∈ U) : Monoid.End U :=
  restrictedFrobenius T U stable

/-- Every restricted power has its original ambient value. -/
theorem componentEnd_pow_value (T : Monoid.End B) (U : Subgroup B)
    (stable : ∀ x ∈ U, T x ∈ U) (n : ℕ) (x : U) :
    ((componentEnd T U stable ^ n) x).1 = (T ^ n) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ']
      change T ((componentEnd T U stable ^ n) x).1 = T ((T ^ n) x.1)
      exact congrArg T ih

/-- The single stability statement implies stability of every power. -/
theorem component_power_stable (T : Monoid.End B) (U : Subgroup B)
    (stable : ∀ x ∈ U, T x ∈ U) (n : ℕ) (x : B) (hx : x ∈ U) :
    (T ^ n) x ∈ U := by
  rw [← componentEnd_pow_value T U stable n ⟨x, hx⟩]
  exact ((componentEnd T U stable ^ n) ⟨x, hx⟩).2

/-- Powers commute, so the return power acts on the defining fixed subgroup. -/
def fixedPowerEnd (T : Monoid.End B) (r s : ℕ) :
    Monoid.End (fixedPoints (T ^ s)) where
  toFun x := ⟨(T ^ r) x.1, by
    change (T ^ s) ((T ^ r) x.1) = (T ^ r) x.1
    calc
      (T ^ s) ((T ^ r) x.1) = (T ^ r) ((T ^ s) x.1) := by
        change (T ^ s * T ^ r) x.1 = (T ^ r * T ^ s) x.1
        rw [← pow_add, ← pow_add, Nat.add_comm s r]
      _ = (T ^ r) x.1 := congrArg (T ^ r) x.2⟩
  map_one' := Subtype.ext ((T ^ r).map_one)
  map_mul' x y := Subtype.ext ((T ^ r).map_mul x.1 y.1)

@[simp] theorem fixedPowerEnd_value (T : Monoid.End B) (r s : ℕ)
    (x : fixedPoints (T ^ s)) :
    (fixedPowerEnd T r s x).1 = (T ^ r) x.1 := rfl

/-- Reorder the two literal membership proofs, with the actual defining map. -/
def fixedComponentEquiv (T Ψ : Monoid.End B) (U : Subgroup B)
    (stable : ∀ x ∈ U, T x ∈ U) (s : ℕ) (defining_eq : Ψ = T ^ s) :
    fixedPoints (componentEnd T U stable ^ s) ≃* rationalSubgroup Ψ U where
  toFun x := ⟨⟨x.1.1, by
    change Ψ x.1.1 = x.1.1
    rw [defining_eq]
    exact (componentEnd_pow_value T U stable s x.1).symm.trans
      (congrArg Subtype.val x.2)⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, by
    apply Subtype.ext
    change ((componentEnd T U stable ^ s) ⟨x.1.1, x.2⟩).1 = x.1.1
    rw [componentEnd_pow_value]
    exact (congrArg (fun f : Monoid.End B ↦ f x.1.1) defining_eq).symm.trans x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem fixedComponentEquiv_value (T Ψ : Monoid.End B) (U : Subgroup B)
    (stable : ∀ x ∈ U, T x ∈ U) (s : ℕ) (defining_eq : Ψ = T ^ s)
    (x : fixedPoints (componentEnd T U stable ^ s)) :
    (fixedComponentEquiv T Ψ U stable s defining_eq x).1.1 = x.1.1 := rfl

@[simp] theorem fixedComponentEquiv_symm_value (T Ψ : Monoid.End B) (U : Subgroup B)
    (stable : ∀ x ∈ U, T x ∈ U) (s : ℕ) (defining_eq : Ψ = T ^ s)
    (x : rationalSubgroup Ψ U) :
    ((fixedComponentEquiv T Ψ U stable s defining_eq).symm x).1.1 = x.1.1 := rfl

/-- On the literal component fixed points, the corrected return has the exact
ambient value given by the original Frobenius maps. -/
theorem component_return_value (F0 F : Monoid.End B) (U : Subgroup B)
    (h u v q r d s : ℕ) (hF : F = F0 ^ h)
    (return_exponent : v + h * q = u * r) (fixed_exponent : h * d = u * s)
    (stable : ∀ x ∈ U, (F0 ^ u) x ∈ U)
    (x : fixedPoints (componentEnd (F0 ^ u) U stable ^ s)) :
    let e := fixedComponentEquiv (F0 ^ u) (F ^ d) U stable s
      (defining_power F0 F h u d s hF fixed_exponent)
    (e (fixedPowerEnd (componentEnd (F0 ^ u) U stable) r s x)).1.1 =
      (F ^ q) ((F0 ^ v) (e x).1.1) := by
  dsimp only
  change ((componentEnd (F0 ^ u) U stable ^ r) x.1).1 =
    (F ^ q) ((F0 ^ v) x.1.1)
  rw [componentEnd_pow_value]
  exact (congrArg (fun f : Monoid.End B ↦ f x.1.1)
    (corrected_power F0 F h u v q r hF return_exponent)).symm

/-- An already given coordinate-return map is identified by its original
ambient square, without a field-action or normalized-return assumption. -/
theorem coordinate_return_square (F0 F : Monoid.End B) (U : Subgroup B)
    (h u v q r d s : ℕ) (hF : F = F0 ^ h)
    (return_exponent : v + h * q = u * r) (fixed_exponent : h * d = u * s)
    (stable : ∀ x ∈ U, (F0 ^ u) x ∈ U)
    (returnMap : Monoid.End (rationalSubgroup (F ^ d) U))
    (return_value : ∀ y, (returnMap y).1.1 = (F ^ q) ((F0 ^ v) y.1.1))
    (x : fixedPoints (componentEnd (F0 ^ u) U stable ^ s)) :
    let e := fixedComponentEquiv (F0 ^ u) (F ^ d) U stable s
      (defining_power F0 F h u d s hF fixed_exponent)
    returnMap (e x) = e (fixedPowerEnd (componentEnd (F0 ^ u) U stable) r s x) := by
  dsimp only
  apply Subtype.ext
  apply Subtype.ext
  exact (return_value _).trans
    (component_return_value F0 F U h u v q r d s hF
      return_exponent fixed_exponent stable x).symm

/-- One Lang adjustment simultaneously normalizes the return and defining
maps. Their standard powers use the same embedding and conjugating element. -/
theorem normalized_simultaneous_powers (j : S →* B)
    (F0 F : Monoid.End B) (Φ : Monoid.End S)
    (h u v q r d s : ℕ) (hF : F = F0 ^ h)
    (return_exponent : v + h * q = u * r) (fixed_exponent : h * d = u * s)
    (c : S) (generator_value : ∀ x, (F0 ^ u) (j x) = j (c * Φ x * c⁻¹))
    (a : S) (lang_value : Φ a * a⁻¹ = c⁻¹) :
    (∀ x, (F ^ q) ((F0 ^ v) (adjustedEmbedding j a x)) =
      adjustedEmbedding j a ((Φ ^ r) x)) ∧
    (∀ x, (F ^ d) (adjustedEmbedding j a x) =
      adjustedEmbedding j a ((Φ ^ s) x)) := by
  have square : ∀ x, (F0 ^ u) (adjustedEmbedding j a x) =
      adjustedEmbedding j a (Φ x) :=
    adjustedEmbedding_frobenius j (F0 ^ u) Φ c generator_value a lang_value
  constructor
  · intro x
    change ((F ^ q).comp (F0 ^ v)) (adjustedEmbedding j a x) = _
    rw [corrected_power F0 F h u v q r hF return_exponent]
    exact intertwining_power (adjustedEmbedding j a) (F0 ^ u) Φ square r x
  · intro x
    rw [defining_power F0 F h u d s hF fixed_exponent]
    exact intertwining_power (adjustedEmbedding j a) (F0 ^ u) Φ square s x

end ModularRep.PaperProofs.TypeBLeviReturnPowerFixedPoints


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
