import ModularRep.CentralCharacterIdempotent

/-!
# Orthogonality of finite linear characters

This file proves the elementary translation formula for the sum of the values
of a linear character of a finite group.  It then applies that formula to the
central character idempotents in a group algebra.
-/

open scoped BigOperators

namespace ModularRep

noncomputable section

section CharacterSums

variable {k Z : Type*} [Field k] [Group Z] [Fintype Z]

local instance characterDecidableEq : DecidableEq (Z →* kˣ) := Classical.decEq _

/-- The values of a nontrivial linear character of a finite group sum to zero.

The argument translates the sum by an element on which the character is not
one.  Commutativity of `Z` is not required.
-/
theorem sum_linearCharacter_eq_zero_of_ne_one (chi : Z →* kˣ) (hchi : chi ≠ 1) :
    ∑ z : Z, (chi z : k) = 0 := by
  classical
  have hexists : ∃ z : Z, chi z ≠ 1 := by
    by_contra h
    apply hchi
    apply MonoidHom.ext
    intro z
    by_contra hz
    exact (not_exists.mp h z) hz
  obtain ⟨a, ha⟩ := hexists
  have ha' : (chi a : k) ≠ 1 := fun h ↦ ha (Units.ext h)
  apply eq_zero_of_mul_eq_self_left ha'
  calc
    (chi a : k) * ∑ z : Z, (chi z : k) =
        ∑ z : Z, (chi (a * z) : k) := by
          rw [Finset.mul_sum]
          simp only [map_mul, Units.val_mul]
    _ = ∑ z : Z, (chi z : k) :=
      Equiv.sum_comp (Equiv.mulLeft a) (fun z : Z ↦ (chi z : k))

/-- The sum of the values of a finite linear character is the order of the
group for the trivial character and zero for every nontrivial character. -/
theorem sum_linearCharacter_eq_ite (chi : Z →* kˣ) :
    ∑ z : Z, (chi z : k) =
      if chi = 1 then (Fintype.card Z : k) else 0 := by
  classical
  split_ifs with hchi
  · subst chi
    simp
  · exact sum_linearCharacter_eq_zero_of_ne_one chi hchi

/-- Distinct linear characters are orthogonal under the unnormalised pairing
`(nu, mu) ↦ ∑ z, nu(z)⁻¹ mu(z)`.
-/
theorem sum_linearCharacter_inv_mul_eq_zero (nu mu : Z →* kˣ) (h : nu ≠ mu) :
    ∑ z : Z, ((((nu z)⁻¹ * mu z : kˣ) : k)) = 0 := by
  let chi : Z →* kˣ := nu⁻¹ * mu
  have hchi : chi ≠ 1 := by
    intro hchi
    apply h
    exact inv_mul_eq_one.mp hchi
  simpa [chi] using sum_linearCharacter_eq_zero_of_ne_one chi hchi

end CharacterSums

section GroupAlgebra

open MonoidAlgebra

variable {k G : Type*} [Field k] [Group G]

/-- Multiplication of two character-weighted sums is controlled by the
unnormalised pairing of their characters. -/
theorem linearCharacterWeightedSum_mul (Z : Subgroup G) [Fintype Z]
    (nu mu : Z →* kˣ) :
    linearCharacterWeightedSum Z nu * linearCharacterWeightedSum Z mu =
      (∑ z : Z, ((((nu z)⁻¹ * mu z : kˣ) : k))) •
        linearCharacterWeightedSum Z mu := by
  classical
  change (∑ x : Z, single (x : G) (((nu x)⁻¹ : kˣ) : k)) *
      (∑ y : Z, single (y : G) (((mu y)⁻¹ : kˣ) : k)) = _
  rw [Fintype.sum_mul_sum]
  simp_rw [MonoidAlgebra.single_mul_single]
  have hinner (x : Z) :
      (∑ y : Z, single ((x : G) * (y : G))
        ((((nu x)⁻¹ : kˣ) : k) * (((mu y)⁻¹ : kˣ) : k))) =
        ((((nu x)⁻¹ * mu x : kˣ) : k)) •
          linearCharacterWeightedSum Z mu := by
    rw [linearCharacterWeightedSum, Finset.smul_sum]
    calc
      (∑ y : Z, single ((x : G) * (y : G))
          ((((nu x)⁻¹ : kˣ) : k) * (((mu y)⁻¹ : kˣ) : k))) =
          ∑ y : Z, single (((Equiv.mulLeft x) y : Z) : G)
            (((((nu x)⁻¹ * mu x * (mu ((Equiv.mulLeft x) y))⁻¹ : kˣ) : k))) := by
              apply Finset.sum_congr rfl
              intro y _
              apply congrArg (single ((x : G) * (y : G)))
              change (((nu x)⁻¹ * (mu y)⁻¹ : kˣ) : k) =
                ((nu x)⁻¹ * mu x * (mu (x * y))⁻¹ : kˣ)
              apply congrArg Units.val
              rw [map_mul, mul_inv_rev]
              symm
              calc
                (nu x)⁻¹ * mu x * ((mu y)⁻¹ * (mu x)⁻¹) =
                    (mu x * (mu x)⁻¹) * ((nu x)⁻¹ * (mu y)⁻¹) := by
                      ac_rfl
                _ = (nu x)⁻¹ * (mu y)⁻¹ := by simp
      _ = ∑ t : Z, single (t : G)
          (((((nu x)⁻¹ * mu x * (mu t)⁻¹ : kˣ) : k))) :=
        Equiv.sum_comp (Equiv.mulLeft x)
          (fun t : Z ↦ single (t : G)
            (((((nu x)⁻¹ * mu x * (mu t)⁻¹ : kˣ) : k))))
      _ = ∑ t : Z, ((((nu x)⁻¹ * mu x : kˣ) : k)) •
          single (t : G) (((mu t)⁻¹ : kˣ) : k) := by
            apply Finset.sum_congr rfl
            intro t _
            simp only [MonoidAlgebra.smul_single', Units.val_mul]
  simp_rw [hinner]
  rw [← Finset.sum_smul]

/-- Character-weighted sums attached to distinct linear characters multiply
to zero. -/
theorem linearCharacterWeightedSum_mul_eq_zero (Z : Subgroup G) [Fintype Z]
    (nu mu : Z →* kˣ) (h : nu ≠ mu) :
    linearCharacterWeightedSum Z nu * linearCharacterWeightedSum Z mu = 0 := by
  rw [linearCharacterWeightedSum_mul,
    sum_linearCharacter_inv_mul_eq_zero nu mu h, zero_smul]

/-- The central character idempotents attached to distinct linear characters
are orthogonal. -/
theorem centralCharacterIdempotent_mul_eq_zero (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (nu mu : Z →* kˣ) (h : nu ≠ mu) :
    centralCharacterIdempotent Z nu * centralCharacterIdempotent Z mu = 0 := by
  rw [centralCharacterIdempotent_eq_weightedSum,
    centralCharacterIdempotent_eq_weightedSum, smul_mul_smul_comm,
    linearCharacterWeightedSum_mul_eq_zero Z nu mu h, smul_zero]

end GroupAlgebra

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
