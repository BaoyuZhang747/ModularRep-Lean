import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Sufficient ordinary roots for the actual Spin group

The constructed Spin projection onto matrix Omega has exactly two kernel
elements, the literal scalar signs. Its quotient cardinality and the actual
index-two Omega inclusion give equal Spin and SO orders. The sufficient-root
instance is transported in the same coefficient field by that equality.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinSOOrdinaryRoots

open TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding
open TypeBOrthogonalOmegaCarriers

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  (N : NormSource n F) (parameters : OddFieldParameters F p f)
  (rank : 3 ≤ n) (C : Source n F p f parameters rank N)

/-- The actual projection kernel has its two distinct scalar signs. -/
theorem spinProjection_kernel_card :
    Nat.card (spinProjection n F parameters rank N C).ker = 2 := by
  apply (Nat.card_eq_two_iff'
    (1 : (spinProjection n F parameters rank N C).ker)).mpr
  let minus : (spinProjection n F parameters rank N C).ker :=
    ⟨minusOneSpin n F N,
      (spinProjection_eq_one_iff n F N parameters rank C _).mpr (Or.inr rfl)⟩
  refine ⟨minus, ?_, ?_⟩
  · intro equal
    exact minusOneSpin_ne_one n F N parameters (congrArg Subtype.val equal)
  · intro x different
    apply Subtype.ext
    change x.val = minusOneSpin n F N
    have nonidentity : x.val ≠ 1 := by
      intro equal
      exact different (Subtype.ext equal)
    exact ((spinProjection_eq_one_iff n F N parameters rank C x.val).mp
      x.property).resolve_left nonidentity

include C in
/-- The first isomorphism theorem counts the actual Spin projection. -/
theorem spin_card_eq_two_mul_omega_card :
    Nat.card (Spin n F N) = 2 * Nat.card (Omega n F) := by
  have quotientCard := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective
      (spinProjection n F parameters rank N C)
      (spinProjection_surjective n F parameters rank N C)).toEquiv
  calc
    Nat.card (Spin n F N) =
        Nat.card (Spin n F N ⧸ (spinProjection n F parameters rank N C).ker) *
          Nat.card (spinProjection n F parameters rank N C).ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = Nat.card (Omega n F) * 2 := by
      rw [quotientCard, spinProjection_kernel_card N parameters rank C]
    _ = 2 * Nat.card (Omega n F) := Nat.mul_comm _ _

/-- The separate matrix inclusion supplies the SO order. -/
theorem so_card_eq_two_mul_omega_card
    (indexTwo : (omegaSubgroup n F).index = 2) :
    Nat.card (SpecialOrthogonal n F) = 2 * Nat.card (Omega n F) := by
  simpa only [indexTwo] using (omegaSubgroup n F).index_mul_card.symm

include C in
/-- The two cardinalities agree through their common actual Omega carrier. -/
theorem spin_card_eq_so_card
    (indexTwo : (omegaSubgroup n F).index = 2) :
    Nat.card (Spin n F N) = Nat.card (SpecialOrthogonal n F) :=
  (spin_card_eq_two_mul_omega_card N parameters rank C).trans
    (so_card_eq_two_mul_omega_card indexTwo).symm

/-- The finite matrix SO carrier also proves finiteness of this Spin carrier. -/
def spinFinite (indexTwo : (omegaSubgroup n F).index = 2) : Finite (Spin n F N) := by
  apply Nat.finite_of_card_ne_zero
  rw [spin_card_eq_so_card N parameters rank C indexTwo]
  exact Nat.card_pos.ne'

/-- Sufficient SO roots supply Spin roots in exactly the same field. -/
def spinOrdinaryRoots {K : Type} [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (SpecialOrthogonal n F))]
    (indexTwo : (omegaSubgroup n F).index = 2) :
    HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) := by
  rw [spin_card_eq_so_card N parameters rank C indexTwo]
  infer_instance

end ModularRep.PaperProofs.TypeBSpinSOOrdinaryRoots


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
