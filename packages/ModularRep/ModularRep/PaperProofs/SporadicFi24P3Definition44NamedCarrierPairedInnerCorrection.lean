import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction

/-! # Compatible inner corrections of the original and quotient actions -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPairedInnerCorrection

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction

universe u

theorem innerCorrection_square
    {X Y : Type u} [Group X] [Group Y]
    (f : X →* Y) (tau : MulAut X) (tauD : MulAut Y)
    (square : ∀ x, f (tau x) = tauD (f x)) (g x : X) :
    f ((tau * MulAut.conj g) x) =
      (tauD * MulAut.conj (f g)) (f x) := by
  change f (tau (g * x * g⁻¹)) = tauD (f g * f x * (f g)⁻¹)
  simpa only [map_mul, map_inv] using square (g * x * g⁻¹)

theorem exists_compatible_innerCorrection
    {p : ℕ} {X Y : Type u} [Group X] [Group Y]
    (f : X →* Y) (tau : MulAut X) (tauD : MulAut Y)
    (square : ∀ x, f (tau x) = tauD (f x))
    (Q : RadicalSubgroup (p := p) (G := X))
    (hfixed : MulOpposite.op tau •
        (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' Q) :
    ∃ g : X,
      Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1 ∧
      (Q.1.map f).comap (tauD * MulAut.conj (f g)).toMonoidHom = Q.1.map f ∧
      ∀ x, f ((tau * MulAut.conj g) x) =
        (tauD * MulAut.conj (f g)) (f x) := by
  obtain ⟨g, stableU⟩ := exists_innerCorrection_of_fixed_radicalClass Q tau hfixed
  have correctedSquare := innerCorrection_square f tau tauD square g
  exact ⟨g, stableU,
    image_stable f (tau * MulAut.conj g) (tauD * MulAut.conj (f g))
      correctedSquare Q.1 stableU, correctedSquare⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPairedInnerCorrection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
