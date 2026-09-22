import ModularRep.CyclicOuterBrauerExtension

/-!
# Conjugation on the canonical normal-factor copy

The canonical copy of the normal factor in a semidirect-product stabiliser
is preserved by conjugation.  Under the canonical equivalence, conjugation
is exactly the ambient automorphism induced by the semidirect-product
element.  This group-theoretic square is independent of the character or
set of weights used to define the stabiliser.
-/

namespace ModularRep.PaperProofs.CyclicOuterLemma37Concrete

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW

universe u

/-- Conjugation on the canonical embedded copy of the normal factor agrees
with the automorphism induced by the ambient semidirect-product element. -/
theorem canonicalEmbedded_conjugationSquare
    {p : ℕ} {H E X : Type u}
    [Group H] [Group E]
    (phi : E →* MulAut H)
    [MulAction (H ⋊[phi] E) X]
    (x : X)
    (hfixed : ∀ h : H,
      (SemidirectProduct.inl h : H ⋊[phi] E) • x = x)
    (d : semidirectStabilizer (phi := phi) x)
    (y : PrimeRegularElement
      (G := embeddedHStabilizer (phi := phi) x) p) :
    let eH := canonicalHToEmbeddedEquiv x hfixed
    PrimeRegularElement.map eH.symm.toMonoidHom
        (PrimeRegularElement.map (MulAut.conjNormal d).toMonoidHom y) =
      PrimeRegularElement.map
        (semidirectToMulAut phi (d : H ⋊[phi] E)).toMonoidHom
        (PrimeRegularElement.map eH.symm.toMonoidHom y) := by
  dsimp only
  rcases y with ⟨⟨y, ⟨h, rfl⟩⟩, hy⟩
  apply Subtype.ext
  change
    ((d.1 * SemidirectProduct.inl h.1 * d.1⁻¹ : H ⋊[phi] E).left) =
      semidirectToMulAut phi d.1 h.1
  have hd : semidirectToMulAut phi d.1 =
      MulAut.conj d.1.left * phi d.1.right := by
    calc
      semidirectToMulAut phi d.1 =
          semidirectToMulAut phi
            (SemidirectProduct.inl d.1.left *
              SemidirectProduct.inr d.1.right) :=
        congrArg (semidirectToMulAut phi)
          (SemidirectProduct.inl_left_mul_inr_right d.1).symm
      _ = MulAut.conj d.1.left * phi d.1.right := by
        rw [map_mul, semidirectToMulAut_inl, semidirectToMulAut_inr]
  rw [hd]
  simp [MulAut.conj_apply, mul_assoc]

end ModularRep.PaperProofs.CyclicOuterLemma37Concrete


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
