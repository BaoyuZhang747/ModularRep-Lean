import Mathlib.RepresentationTheory.Character

/-!
# Kernel containment from finite group character averaging

This neutral module proves that a finite subgroup on which a representation
character is constantly its degree acts trivially.  No irreducibility,
centrality, character correspondence, block, weight, or manuscript source is
used.
-/

noncomputable section

namespace Representation

universe u

private theorem apply_eq_id_of_character_eq_one
    {K G H V : Type u} [Field K] [CharZero K]
    [Group G] [Group H] [Finite H]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K G V) (f : H →* G)
    (hchar : ∀ h : H,
      rho.character (f h) = rho.character (1 : G)) :
    ∀ h : H, rho (f h) = LinearMap.id := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Invertible (Nat.card H : K) :=
    invertibleOfNonzero (NeZero.ne (Nat.card H : K))
  let rhoH : Representation K H V := rho.comp f
  have hcharH : ∀ h : H,
      rhoH.character h = rhoH.character (1 : H) := by
    intro h
    change rho.character (f h) = rho.character (f 1)
    simpa using hchar h
  have hdimCast :
      (Module.finrank K rhoH.invariants : K) =
        (Module.finrank K V : K) := by
    rw [← rhoH.card_inv_mul_sum_char_eq_finrank]
    simp_rw [hcharH]
    simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, nsmul_eq_mul, Representation.char_one]
    rw [← mul_assoc, inv_mul_cancel_of_invertible, one_mul]
  have hdim :
      Module.finrank K rhoH.invariants = Module.finrank K V := by
    apply Nat.cast_injective (R := K)
    exact hdimCast
  have htop : rhoH.invariants = ⊤ :=
    Submodule.eq_top_of_finrank_eq hdim
  intro h
  ext v
  have hv : v ∈ rhoH.invariants := by
    rw [htop]
    exact Submodule.mem_top
  simpa [rhoH] using
    ((Representation.mem_invariants rhoH v).mp hv h)

/-- A finite subgroup on which the representation character is constantly
its value at the identity lies in the representation kernel. -/
theorem subgroup_le_ker_of_character_eq_one
    {K G V : Type u} [Field K] [CharZero K] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K G V) (S : Subgroup G) [Finite S]
    (hchar : ∀ s : S,
      rho.character (s : G) = rho.character (1 : G)) :
    S ≤ rho.ker := by
  intro g hg
  change rho g = 1
  simpa [Module.End.one_eq_id] using
    (apply_eq_id_of_character_eq_one rho S.subtype hchar ⟨g, hg⟩)

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
