import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.RingTheory.Idempotents

/-!
# Central character idempotents in a group algebra

For a finite subgroup `Z ≤ G` and a multiplicative character
`nu : Z →* kˣ`, this file defines

`(1 / |Z|) ∑ z : Z, nu(z)⁻¹ z ∈ k[G]`.

The definition only needs `Z` to be finite and its order to be invertible in
`k`.  Centrality in `k[G]` additionally assumes `Z ≤ Z(G)`.  No assertion
about completeness as `nu` varies is made.
-/

open scoped BigOperators

namespace ModularRep

open MonoidAlgebra

variable {k G : Type*} [Field k] [Group G]

/-- The unnormalised character-weighted sum `∑ z, nu(z)⁻¹ z`. -/
noncomputable def linearCharacterWeightedSum (Z : Subgroup G) [Fintype Z]
    (nu : Z →* kˣ) : k[G] :=
  ∑ z : Z, single (z : G) (((nu z)⁻¹ : kˣ) : k)

/-- The standard group algebra element attached to a linear character of a
finite subgroup.

The convention is
`|Z|⁻¹ ∑ z : Z, nu(z)⁻¹ z`.
-/
noncomputable def centralCharacterIdempotent (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (nu : Z →* kˣ) : k[G] :=
  ⅟(Fintype.card Z : k) • linearCharacterWeightedSum Z nu

theorem centralCharacterIdempotent_eq_weightedSum (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (nu : Z →* kˣ) :
    centralCharacterIdempotent Z nu =
      ⅟(Fintype.card Z : k) • linearCharacterWeightedSum Z nu :=
  rfl

@[simp]
theorem centralCharacterIdempotent_coeff_coe (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (nu : Z →* kˣ) (z : Z) :
    (centralCharacterIdempotent Z nu).coeff (z : G) =
      ⅟(Fintype.card Z : k) * (((nu z)⁻¹ : kˣ) : k) := by
  classical
  rw [centralCharacterIdempotent, coeff_smul_apply]
  change ⅟(Fintype.card Z : k) * (linearCharacterWeightedSum Z nu).coeff (z : G) = _
  congr 1
  simp only [linearCharacterWeightedSum, coeff_sum]
  let f : Z → G →₀ k := fun w ↦
    (single (w : G) (((nu w)⁻¹ : kˣ) : k)).coeff
  change (∑ w : Z, f w) (z : G) = _
  rw [show (∑ w : Z, f w) (z : G) = ∑ w : Z, f w (z : G) by
    exact Finsupp.finsetSum_apply (Finset.univ : Finset Z) f (z : G)]
  simp only [f, coeff_single, Finsupp.single_apply]
  rw [Fintype.sum_eq_single z]
  · simp
  · intro w hw
    simp [Subtype.coe_injective.ne hw]

theorem centralCharacterIdempotent_coeff_of_not_mem (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (nu : Z →* kˣ) {g : G} (hg : g ∉ Z) :
    (centralCharacterIdempotent Z nu).coeff g = 0 := by
  classical
  have hne : ∀ z : Z, (z : G) ≠ g := by
    intro z hzg
    exact hg (hzg ▸ z.property)
  rw [centralCharacterIdempotent, coeff_smul_apply]
  change ⅟(Fintype.card Z : k) * (linearCharacterWeightedSum Z nu).coeff g = 0
  simp [linearCharacterWeightedSum, hne]

private theorem linearCharacterWeightedSum_mul_self (Z : Subgroup G) [Fintype Z]
    (nu : Z →* kˣ) :
    linearCharacterWeightedSum Z nu * linearCharacterWeightedSum Z nu =
      (Fintype.card Z : k) • linearCharacterWeightedSum Z nu := by
  classical
  rw [linearCharacterWeightedSum, Fintype.sum_mul_sum]
  simp_rw [MonoidAlgebra.single_mul_single]
  have hinner (x : Z) :
      (∑ y : Z, single ((x : G) * (y : G))
        ((((nu x)⁻¹ : kˣ) : k) * (((nu y)⁻¹ : kˣ) : k))) =
        linearCharacterWeightedSum Z nu := by
    simpa [linearCharacterWeightedSum, map_mul, mul_comm] using
      Equiv.sum_comp (Equiv.mulLeft x)
        (fun y : Z ↦ single (y : G) (((nu y)⁻¹ : kˣ) : k))
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
    linearCharacterWeightedSum]

/-- The normalized character-weighted element is idempotent.  Centrality of
`Z` is not needed for this assertion. -/
theorem centralCharacterIdempotent_isIdempotentElem (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (nu : Z →* kˣ) :
    IsIdempotentElem (centralCharacterIdempotent Z nu) := by
  rw [IsIdempotentElem, centralCharacterIdempotent, smul_mul_smul_comm,
    linearCharacterWeightedSum_mul_self, smul_smul, mul_assoc, invOf_mul_self, mul_one]

/-- If `Z` is contained in the centre of `G`, its character-weighted element
is central in the group algebra. -/
theorem centralCharacterIdempotent_mem_center (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (nu : Z →* kˣ)
    (hZ : Z ≤ Subgroup.center G) :
    centralCharacterIdempotent Z nu ∈ Set.center k[G] := by
  rw [Semigroup.mem_center_iff]
  intro a
  apply Commute.eq
  apply Commute.symm
  rw [centralCharacterIdempotent]
  apply Commute.smul_left
  apply Commute.sum_left
  intro z _
  apply MonoidAlgebra.single_commute
  · intro g
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp (hZ z.property) g).symm
  · exact fun r ↦ Commute.all _ r

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
