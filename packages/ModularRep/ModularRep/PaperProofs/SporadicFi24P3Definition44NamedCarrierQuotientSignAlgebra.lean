import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLinearCharacterAlgebra
import ModularRep.CentralCharacterCovering
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.GroupWithZero.Idempotent

/-! The sign of an index-two quotient and the supported trace of an actual
central element. Nonvanishing at a selected block uses only idempotence
and the fact that two is nonzero in the coefficient field. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientSignAlgebra

open ModularRep
open SporadicFi24P3Definition44NamedCarrierLinearCharacterAlgebra

variable {k G : Type*} [Field k] [Group G]

def quotientSign (N : Subgroup G) (hindex : N.index = 2) : G →* kˣ := by
  classical
  exact
    { toFun := fun g => if g ∈ N then 1 else -1
      map_one' := by simp
      map_mul' := by
        intro a b
        by_cases ha : a ∈ N <;> by_cases hb : b ∈ N <;>
          simp [N.mul_mem_iff_of_index_two hindex, ha, hb] }

@[simp]
theorem quotientSign_mem (N : Subgroup G) (hindex : N.index = 2)
    (g : G) (hg : g ∈ N) : quotientSign (k := k) N hindex g = 1 := by
  classical
  simp [quotientSign, hg]

@[simp]
theorem quotientSign_not_mem (N : Subgroup G) (hindex : N.index = 2)
    (g : G) (hg : g ∉ N) : quotientSign (k := k) N hindex g = -1 := by
  classical
  simp [quotientSign, hg]

theorem quotientSign_square (N : Subgroup G) (hindex : N.index = 2) (g : G) :
    (quotientSign (k := k) N hindex g : k) *
      (quotientSign (k := k) N hindex g : k) = 1 := by
  by_cases hg : g ∈ N <;> simp [hg]

def centerSign (N : Subgroup G) (hindex : N.index = 2) :
    GroupAlgebraCenter k G ≃ₐ[k] GroupAlgebraCenter k G :=
  centerTwist (quotientSign N hindex) (quotientSign_square N hindex)

@[simp]
theorem centerSign_coe (N : Subgroup G) (hindex : N.index = 2)
    (z : GroupAlgebraCenter k G) :
    (centerSign N hindex z : k[G]) =
      algebraTwist (quotientSign N hindex) (z : k[G]) := rfl

theorem centerSign_trace_supported (N : Subgroup G) (hindex : N.index = 2)
    (z : GroupAlgebraCenter k G) :
    CentralElementSupportedOn N (z + centerSign N hindex z) := by
  intro g hg
  change z.val.coeff g +
    (algebraTwist (quotientSign N hindex) z.val).coeff g = 0
  rw [algebraTwist_coeff]
  simp [hg]

theorem index_eq_two_of_quotient_card_le_two [Finite G]
    (N : Subgroup G) [N.Normal]
    (hcard : Nat.card (G ⧸ N) ≤ 2) (hN : N ≠ ⊤) :
    N.index = 2 := by
  have hgt := N.one_lt_index_of_ne_top hN
  change N.index ≤ 2 at hcard
  omega

theorem idempotent_trace_ne_zero
    {F A : Type*} [Field F] [Ring A] [Algebra F A]
    (h2 : (2 : F) ≠ 0) (lambda : A →ₐ[F] F) (T : A →ₐ[F] A)
    (e : A) (he : IsIdempotentElem e) (hown : lambda e = 1) :
    lambda (e + T e) ≠ 0 := by
  rw [map_add, hown]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp ((he.map T).map lambda) with h | h
  · simpa only [h, add_zero] using (one_ne_zero : (1 : F) ≠ 0)
  · simpa only [h, one_add_one_eq_two] using h2

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientSignAlgebra


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
