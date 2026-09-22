import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Subgroup subconjugacy

This file records the elementary subgroup relations used by the block-defect
interface.  The orientation is fixed: `P.IsSubconjugate Q` means that `P` is
contained in a conjugate of `Q`, namely in `g Q g⁻¹` for some `g`.

The file is purely group-theoretic.  In particular, it does not import any
character, block, or manuscript-application module.
-/

namespace Subgroup

universe u

variable {G : Type u} [Group G]

/-- `P.IsSubconjugate Q` means that `P` is contained in `g Q g⁻¹` for
some `g : G`. -/
def IsSubconjugate (P Q : Subgroup G) : Prop :=
  ∃ g : G, P ≤ Q.map (MulAut.conj g).toMonoidHom

/-- Two subgroups are conjugate when one is the image of the other under an
inner automorphism. -/
def AreConjugate (P Q : Subgroup G) : Prop :=
  ∃ g : G, P = Q.map (MulAut.conj g).toMonoidHom

/-- Every subgroup is subconjugate to itself. -/
theorem IsSubconjugate.refl (P : Subgroup G) : P.IsSubconjugate P := by
  exact ⟨1, by simp [MulAut.one_def]⟩

/-- Subconjugacy is transitive.  With the chosen orientation, witnesses
`g` and `h` compose to the witness `g * h`. -/
theorem IsSubconjugate.trans {P Q R : Subgroup G}
    (hPQ : P.IsSubconjugate Q) (hQR : Q.IsSubconjugate R) :
    P.IsSubconjugate R := by
  rcases hPQ with ⟨g, hg⟩
  rcases hQR with ⟨h, hh⟩
  refine ⟨g * h, fun x hx => ?_⟩
  rcases hg hx with ⟨y, hy, rfl⟩
  rcases hh hy with ⟨z, hz, rfl⟩
  refine ⟨z, hz, ?_⟩
  change MulAut.conj (g * h) z = MulAut.conj g (MulAut.conj h z)
  simp only [map_mul, MulAut.mul_apply]

/-- Every subgroup is conjugate to itself. -/
theorem AreConjugate.refl (P : Subgroup G) : P.AreConjugate P := by
  exact ⟨1, by simp [MulAut.one_def]⟩

/-- Subgroup conjugacy is symmetric. -/
theorem AreConjugate.symm {P Q : Subgroup G}
    (hPQ : P.AreConjugate Q) : Q.AreConjugate P := by
  rcases hPQ with ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  ext x
  simp only [Subgroup.mem_map_equiv, map_inv, MulAut.inv_symm,
    MulEquiv.symm_apply_apply]

/-- Subgroup conjugacy is transitive. -/
theorem AreConjugate.trans {P Q R : Subgroup G}
    (hPQ : P.AreConjugate Q) (hQR : Q.AreConjugate R) :
    P.AreConjugate R := by
  rcases hPQ with ⟨g, rfl⟩
  rcases hQR with ⟨h, rfl⟩
  refine ⟨g * h, ?_⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  change MulAut.conj g (MulAut.conj h x) = MulAut.conj (g * h) x
  simp only [map_mul, MulAut.mul_apply]

/-- Conjugacy implies subconjugacy in the same orientation. -/
theorem AreConjugate.isSubconjugate {P Q : Subgroup G}
    (hPQ : P.AreConjugate Q) : P.IsSubconjugate Q := by
  rcases hPQ with ⟨g, hg⟩
  exact ⟨g, hg.le⟩

/-- Conjugate subgroups are mutually subconjugate. -/
theorem AreConjugate.mutual_isSubconjugate {P Q : Subgroup G}
    (hPQ : P.AreConjugate Q) :
    P.IsSubconjugate Q ∧ Q.IsSubconjugate P :=
  ⟨hPQ.isSubconjugate, hPQ.symm.isSubconjugate⟩

/-- In a finite ambient group, mutual subconjugacy implies conjugacy. -/
theorem IsSubconjugate.areConjugate_of_mutual [Finite G] {P Q : Subgroup G}
    (hPQ : P.IsSubconjugate Q) (hQP : Q.IsSubconjugate P) :
    P.AreConjugate Q := by
  rcases hPQ with ⟨g, hg⟩
  rcases hQP with ⟨h, hh⟩
  refine ⟨g, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge hg
  calc
    Nat.card (Q.map (MulAut.conj g).toMonoidHom) = Nat.card Q :=
      Subgroup.card_map_of_injective (K := Q) (MulAut.conj g).injective
    _ ≤ Nat.card (P.map (MulAut.conj h).toMonoidHom) :=
      Subgroup.card_le_of_le hh
    _ = Nat.card P :=
      Subgroup.card_map_of_injective (K := P) (MulAut.conj h).injective

/-- If `P` is subconjugate to a subgroup `D` that is contained in `P`, then
the two subgroups are equal in a finite ambient group. -/
theorem IsSubconjugate.eq_of_le [Finite G] {P D : Subgroup G}
    (hPD : P.IsSubconjugate D) (hDP : D ≤ P) : D = P := by
  rcases hPD with ⟨g, hg⟩
  apply Subgroup.eq_of_le_of_card_ge hDP
  calc
    Nat.card P ≤ Nat.card (D.map (MulAut.conj g).toMonoidHom) :=
      Subgroup.card_le_of_le hg
    _ = Nat.card D :=
      Subgroup.card_map_of_injective (K := D) (MulAut.conj g).injective

end Subgroup


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
