import ModularRep.PaperProofs.EvenFieldQuotientTriviality
import ModularRep.PaperProofs.EvenFieldSourceShaped

/-!
# Fixed-point relative quotient in manuscript Lemma 3.6

This module formalises the passage in manuscript lines 382--388.  Once the
Weyl-group argument supplies `y⁻¹ sigma(y) in L`, commutation with the defining
Frobenius map puts the calculation inside the finite fixed-point group.  Lean
then proves that the induced action on the corresponding quotient is the
identity.
-/

namespace ModularRep.PaperProofs.EvenFieldFixedQuotient

open ModularRep.PaperProofs.EvenFieldSourceShaped
open ModularRep.PaperProofs.EvenFieldQuotientTriviality

universe u

variable {G : Type u} [Group G]

/-- Restriction of an endomorphism to a stable subgroup. -/
def restrictToStableSubgroup
    {H : Type u} [Group H] (N : Subgroup H) (alpha : H →* H)
    (stable : ∀ x : N, alpha x ∈ N) : N →* N where
  toFun x := ⟨alpha x, stable x⟩
  map_one' := by
    apply Subtype.ext
    exact map_one alpha
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul alpha (x : H) (y : H)

/-- The subgroup `L^F` viewed inside a selected subgroup `N` of `G^F`. -/
def fixedBase
    (F : G →* G) (N : Subgroup (frobeniusFixedSubgroup F))
    (L : Subgroup G) : Subgroup N :=
  L.comap ((frobeniusFixedSubgroup F).subtype.comp N.subtype)

/-- The representative-level Weyl quotient calculation implies that the
induced endomorphism of the finite relative quotient is the identity. -/
theorem relativeQuotientAction_eq_id
    (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (N : Subgroup (frobeniusFixedSubgroup F))
    (N_stable : ∀ x : N,
      frobeniusFixedSubgroupHom F sigma commute x ∈ N)
    (L : Subgroup G)
    [normalB : (fixedBase F N L).Normal]
    (weylDifference : ∀ x : N,
      ((x : frobeniusFixedSubgroup F) : G)⁻¹ *
          sigma ((x : frobeniusFixedSubgroup F) : G) ∈ L) :
    let alphaN := restrictToStableSubgroup N
      (frobeniusFixedSubgroupHom F sigma commute) N_stable
    let B := fixedBase F N L
    let preservesB : ∀ x : B, alphaN x ∈ B := by
      intro x
      change sigma (((x : B) : N) : G) ∈ L
      have hx : (((x : B) : N) : G) ∈ L := x.property
      have hd := weylDifference (x : N)
      have hproduct :
          (((x : B) : N) : G) *
              ((((x : B) : N) : G)⁻¹ *
                sigma (((x : B) : N) : G)) ∈ L :=
        L.mul_mem hx hd
      simpa [mul_assoc] using hproduct
    quotientEndomorphism B alphaN preservesB = MonoidHom.id (N ⧸ B) := by
  dsimp only
  exact quotientEndomorphism_eq_id _ _ _ (fun x => by
    change
      ((((x : N) : frobeniusFixedSubgroup F) : G)⁻¹ *
        sigma (((x : N) : frobeniusFixedSubgroup F) : G)) ∈ L
    exact weylDifference x)

end ModularRep.PaperProofs.EvenFieldFixedQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
