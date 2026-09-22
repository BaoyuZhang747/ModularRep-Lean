import ModularRep.CharacterWeightRadicalProjection
import ModularRep.SubgroupSubconjugacy

/-! Elementary subgroup orders and the literal radical conjugacy quotient.
These statements have no block assignment, character or weight-count input. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3RadicalSupportGeometry
open ModularRep ModularRep.CharacterWeight

theorem card_one_or_three_or_nine
    {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hPQ : P.IsSubconjugate Q) (hQ : Nat.card Q = 9) :
    Nat.card P = 1 ∨ Nat.card P = 3 ∨ Nat.card P = 9 := by
  obtain ⟨g, hg⟩ := hPQ
  have hd := Subgroup.card_dvd_of_le hg
  rw [Subgroup.card_map_of_injective
    (K := Q) (MulAut.conj g).injective, hQ] at hd
  have hd' : Nat.card P ∣ 3 ^ 2 := hd
  obtain ⟨n, hn, heq⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hd'
  have hc : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact Or.inl (by simpa using heq)
  · exact Or.inr (Or.inl (by simpa using heq))
  · exact Or.inr (Or.inr (by simpa using heq))

theorem radicalClass_eq_of_areConjugate
    {p : ℕ} {G : Type*} [Group G]
    (P Q : RadicalSubgroup (p := p) (G := G))
    (hPQ : P.1.AreConjugate Q.1) :
    (Quotient.mk'' P : RadicalConjugacyClass (p := p) (G := G)) =
      Quotient.mk'' Q := by
  obtain ⟨g, hg⟩ := hPQ
  apply Quotient.sound
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change Q.1.comap (MulAut.conj g⁻¹).toMonoidHom = P.1
  rw [Subgroup.comap_equiv_eq_map_symm']
  simpa only [map_inv, MulAut.inv_symm] using hg.symm

theorem radicalClass_eq_of_subconjugate_of_card_eq
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (P Q : RadicalSubgroup (p := p) (G := G))
    (hPQ : P.1.IsSubconjugate Q.1)
    (hcard : Nat.card P.1 = Nat.card Q.1) :
    (Quotient.mk'' P : RadicalConjugacyClass (p := p) (G := G)) =
      Quotient.mk'' Q := by
  obtain ⟨g, hg⟩ := hPQ
  apply radicalClass_eq_of_areConjugate P Q
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [Subgroup.card_map_of_injective
    (K := Q.1) (MulAut.conj g).injective]
  exact hcard.ge

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3RadicalSupportGeometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
