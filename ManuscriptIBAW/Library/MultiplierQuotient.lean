import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# A multiplier and the quotient by the centre

A surjective homomorphism identifies the quotient by its kernel and the
centre with the quotient of its image by the image of the centre. For a
finite field, the subgroup of squares has index at most two. These are the
group and field calculations used before the linear character bound in Lemma
3.10.
-/

noncomputable section

namespace ManuscriptIBAW

universe u v

variable {G : Type u} {U : Type v} [Group G] [CommGroup U]

/-- The isomorphism induced by the multiplier on the two quotient groups. -/
def quotientKernelCenterEquiv (mu : G →* U) (surjective : Function.Surjective mu) :
    G ⧸ (mu.ker ⊔ Subgroup.center G) ≃*
      U ⧸ (Subgroup.center G).map mu := by
  let pi := QuotientGroup.mk' ((Subgroup.center G).map mu)
  let f := pi.comp mu
  have hker : f.ker = mu.ker ⊔ Subgroup.center G := by
    change (pi.comp mu).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_map_eq, sup_comm]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk'_surjective _).comp surjective))

/-- The index of the squares is bounded by the number of roots of `x^2 = 1`. -/
theorem finite_field_squares_index_le_two (F : Type u) [Field F] [Finite F] :
    (powMonoidHom (α := Fˣ) 2).range.index ≤ 2 := by
  rw [Subgroup.index_range, ← rootsOfUnity_eq_ker]
  exact card_rootsOfUnity F 2

/-- In odd characteristic the two roots are `1` and `-1`, so the index is two. -/
theorem finite_field_squares_index_eq_two (F : Type u) [Field F] [Finite F]
    (p : ℕ) [CharP F p] (oddCharacteristic : p ≠ 2) :
    (powMonoidHom (α := Fˣ) 2).range.index = 2 := by
  rw [Subgroup.index_range, ← rootsOfUnity_eq_ker]
  exact (IsPrimitiveRoot.neg_one p oddCharacteristic (R := F)).card_rootsOfUnity

/-- The index bound follows from the kernel and central image of the multiplier. -/
theorem multiplier_index_le_two {F : Type v} [Field F] [Finite F]
    (mu : G →* Fˣ) (surjective : Function.Surjective mu)
    (centralImage : (Subgroup.center G).map mu = (powMonoidHom 2).range) :
    Nat.card (G ⧸ (mu.ker ⊔ Subgroup.center G)) ≤ 2 := by
  rw [Nat.card_congr (quotientKernelCenterEquiv mu surjective).toEquiv]
  change ((Subgroup.center G).map mu).index ≤ 2
  rw [centralImage]
  exact finite_field_squares_index_le_two F

/-- The same quotient calculation gives the exact index in odd characteristic. -/
theorem multiplier_index_eq_two {F : Type v} [Field F] [Finite F]
    (p : ℕ) [CharP F p] (oddCharacteristic : p ≠ 2)
    (mu : G →* Fˣ) (surjective : Function.Surjective mu)
    (centralImage : (Subgroup.center G).map mu = (powMonoidHom 2).range) :
    Nat.card (G ⧸ (mu.ker ⊔ Subgroup.center G)) = 2 := by
  rw [Nat.card_congr (quotientKernelCenterEquiv mu surjective).toEquiv]
  change ((Subgroup.center G).map mu).index = 2
  rw [centralImage]
  exact finite_field_squares_index_eq_two F p oddCharacteristic

end ManuscriptIBAW

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
