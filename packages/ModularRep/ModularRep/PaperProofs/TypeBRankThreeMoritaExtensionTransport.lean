import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Extension transport through a commuting restriction square

An object lifts through one restriction functor exactly when its image
lifts through the other. Full faithfulness reflects the base isomorphism;
essential surjectivity supplies a preimage of an upper object. This is
the category argument underlying Ruhstorfer Remark 1.8(b), after the
literal Morita functors and restriction square have been constructed.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaExtensionTransport

open CategoryTheory

universe uC uD uChat uDhat vC vD vChat vDhat

variable {C : Type uC} {D : Type uD} {Chat : Type uChat} {Dhat : Type uDhat}
  [Category.{vC} C] [Category.{vD} D]
  [Category.{vChat} Chat] [Category.{vDhat} Dhat]

/-- A fully faithful base functor and an essentially surjective upper
functor transport liftability through the displayed square. -/
theorem essentialImage_iff_of_square
    (F : C ⥤ D) (Fhat : Chat ⥤ Dhat)
    (rC : Chat ⥤ C) (rD : Dhat ⥤ D)
    [F.Full] [F.Faithful] [Fhat.EssSurj]
    (square : Fhat ⋙ rD ≅ rC ⋙ F) (V : C) :
    rC.essImage V ↔ rD.essImage (F.obj V) := by
  constructor
  · intro h
    obtain ⟨W, ⟨hW⟩⟩ := h
    exact ⟨Fhat.obj W, ⟨square.app W ≪≫ F.mapIso hW⟩⟩
  · intro h
    obtain ⟨W, ⟨hW⟩⟩ := h
    let Vhat : Chat := Fhat.objPreimage W
    let hhat : Fhat.obj Vhat ≅ W := Fhat.objObjPreimageIso W
    refine ⟨Vhat, ⟨F.preimageIso ?_⟩⟩
    exact (square.app Vhat).symm ≪≫ rD.mapIso hhat ≪≫ hW

end ModularRep.PaperProofs.TypeBRankThreeMoritaExtensionTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
