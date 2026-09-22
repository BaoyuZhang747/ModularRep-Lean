import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedIntertwiner
import Mathlib.GroupTheory.Index

/-! Explicit extension on the two cosets, including the nonsplit square correction. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoExtension

open Representation
open SporadicFi24P3Definition44NamedCarrierNormalizedIntertwiner

theorem exists_hom_of_index_two_operator
    {G M : Type*} [Group G] [Monoid M]
    (N : Subgroup G) [N.Normal] (hindex : N.index = 2)
    (t : G) (ht : t ∉ N) (rho : N →* M) (U : M)
    (hU : ∀ n : N, U * rho n = rho (MulAut.conjNormal t n) * U)
    (hU2 : U * U = rho ⟨t * t, N.mul_self_mem_of_index_two hindex t⟩) :
    ∃ sigma : G →* M, (∀ n : N, sigma (n : G) = rho n) ∧ sigma t = U := by
  classical
  have hcoset (g : G) (hg : g ∉ N) : g * t⁻¹ ∈ N := by
    simp [N.mul_mem_iff_of_index_two hindex, N.inv_mem_iff, hg, ht]
  let n0 (g : G) (hg : g ∉ N) : N := ⟨g * t⁻¹, hcoset g hg⟩
  let q : N := ⟨t * t, N.mul_self_mem_of_index_two hindex t⟩
  have hsq : U * U = rho q := hU2
  let f : G → M := fun g =>
    if hg : g ∈ N then rho ⟨g, hg⟩ else rho (n0 g hg) * U
  have hmem (g : G) (hg : g ∈ N) : f g = rho ⟨g, hg⟩ := by
    simp only [f, dif_pos hg]
  have hnot (g : G) (hg : g ∉ N) : f g = rho (n0 g hg) * U := by
    simp only [f, dif_neg hg]
  have hone : f 1 = 1 := by
    rw [hmem 1 N.one_mem]
    exact map_one rho
  have hmul (a b : G) : f (a * b) = f a * f b := by
    by_cases ha : a ∈ N
    · by_cases hb : b ∈ N
      · have hab : a * b ∈ N := N.mul_mem ha hb
        rw [hmem (a * b) hab, hmem a ha, hmem b hb]
        exact map_mul rho ⟨a, ha⟩ ⟨b, hb⟩
      · have hab : a * b ∉ N := by
          simp [N.mul_mem_iff_of_index_two hindex, ha, hb]
        have hn : n0 (a * b) hab = (⟨a, ha⟩ : N) * n0 b hb := by
          apply Subtype.ext
          change a * b * t⁻¹ = a * (b * t⁻¹)
          exact mul_assoc a b t⁻¹
        rw [hnot (a * b) hab, hmem a ha, hnot b hb, hn, map_mul, mul_assoc]
    · by_cases hb : b ∈ N
      · have hab : a * b ∉ N := by
          simp [N.mul_mem_iff_of_index_two hindex, ha, hb]
        have hn : n0 (a * b) hab =
            n0 a ha * MulAut.conjNormal t (⟨b, hb⟩ : N) := by
          apply Subtype.ext
          change a * b * t⁻¹ = (a * t⁻¹) * (t * b * t⁻¹)
          group
        rw [hnot (a * b) hab, hnot a ha, hmem b hb,
          hn, map_mul, mul_assoc, ← hU ⟨b, hb⟩, ← mul_assoc]
      · have hab : a * b ∈ N := by
          simp [N.mul_mem_iff_of_index_two hindex, ha, hb]
        have hn : (⟨a * b, hab⟩ : N) =
            n0 a ha * MulAut.conjNormal t (n0 b hb) * q := by
          apply Subtype.ext
          change a * b = (a * t⁻¹) * (t * (b * t⁻¹) * t⁻¹) * (t * t)
          group
        rw [hmem (a * b) hab, hnot a ha, hnot b hb,
          hn, map_mul, map_mul, ← hsq]
        calc
          (rho (n0 a ha) * rho (MulAut.conjNormal t (n0 b hb))) * (U * U) =
              rho (n0 a ha) * ((rho (MulAut.conjNormal t (n0 b hb)) * U) * U) := by
                simp only [mul_assoc]
          _ = rho (n0 a ha) * ((U * rho (n0 b hb)) * U) := by rw [← hU]
          _ = (rho (n0 a ha) * U) * (rho (n0 b hb) * U) := by
                simp only [mul_assoc]
  let sigma : G →* M := { toFun := f, map_one' := hone, map_mul' := hmul }
  refine ⟨sigma, ?_, ?_⟩
  · intro n
    exact hmem n n.property
  · change f t = U
    have hn : n0 t ht = 1 := by
      apply Subtype.ext
      exact mul_inv_cancel t
    rw [hnot t ht, hn, map_one, one_mul]

theorem exists_extension_of_quotient_card_le_two
    {k H V : Type*} [Field k] [IsAlgClosed k] [Group H] [Finite H]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {N : Subgroup H} [N.Normal]
    (rho : Representation k N V) (hirr : rho.IsIrreducible)
    (hcard : Nat.card (H ⧸ N) ≤ 2)
    (hinvariant : ConjugationInvariant N rho) : Nonempty (Extension N rho) := by
  classical
  by_cases hN : N = ⊤
  · let f : H →* N :=
      { toFun := fun h => ⟨h, by rw [hN]; trivial⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine ⟨{ representation := rho.comp f
              restrictionEquiv := Representation.Equiv.mk (LinearEquiv.refl k V) ?_ }⟩
    intro n
    rfl
  · have hindex : N.index = 2 := by
      have hgt := N.one_lt_index_of_ne_top hN
      change N.index ≤ 2 at hcard
      exact Nat.le_antisymm hcard (Nat.succ_le_of_lt hgt)
    obtain ⟨t, ht, _⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hindex
    obtain ⟨U, hU, hU2⟩ := exists_normalized_conjugating_operator rho hirr t
      (N.mul_self_mem_of_index_two hindex t) hinvariant
    obtain ⟨sigma, hrestrict, _⟩ :=
      exists_hom_of_index_two_operator N hindex t ht rho U hU hU2
    refine ⟨{ representation := sigma
              restrictionEquiv := Representation.Equiv.mk (LinearEquiv.refl k V) ?_ }⟩
    intro n
    ext v
    change sigma (n : H) v = rho n v
    exact congrArg (fun f : Module.End k V => f v) (hrestrict n)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
