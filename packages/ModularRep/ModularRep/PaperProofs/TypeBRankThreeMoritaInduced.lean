import ModularRep.PaperProofs.TypeBRankThreeMoritaDiagonalEquiv
import Mathlib.RepresentationTheory.Induced

/-!
# Restrict the same honest field action and induce its diagonal module

The chosen subgroup Q is a subgroup of the original actor E. Its two actions
are restrictions of the given actions, and its diagonal representation is a
pullback of one honest representation on the same vector space. The final
object is the installed Rep.ind along the literal diagonal inclusion.

There is no Morita, character, block, extension-of-a-simple or source theorem
input. The inverse-coordinate convention of the installed induction model is
retained in the generator equation.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaInduced

open CategoryTheory
open MulOpposite TypeBRankThreeMoritaDiagonal TypeBRankThreeMoritaDiagonalEquiv

universe u

variable {k G L E V : Type u}
variable [CommRing k] [Group G] [Group L] [Group E]
variable [AddCommGroup V] [Module k V]
variable (aG : E →* MulAut G) (aL : E →* MulAut L)

/-- Include the same base pair and the actual subgroup of the original actor. -/
def subgroupSemidirectEmbedding (Q : Subgroup E) :
    (G × Lᵐᵒᵖ) ⋊[baseAction (aG.comp Q.subtype) (aL.comp Q.subtype)] Q →*
      (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E :=
  SemidirectProduct.map (MonoidHom.id _) Q.subtype (fun _ => rfl)

@[simp] theorem subgroupSemidirectEmbedding_inl (Q : Subgroup E) (x : G × Lᵐᵒᵖ) :
    subgroupSemidirectEmbedding aG aL Q (SemidirectProduct.inl x) =
      SemidirectProduct.inl x := rfl

@[simp] theorem subgroupSemidirectEmbedding_inr (Q : Subgroup E) (q : Q) :
    subgroupSemidirectEmbedding aG aL Q (SemidirectProduct.inr q) =
      SemidirectProduct.inr q.val := rfl

/-- The actual hom for restricting the original honest action to the diagonal. -/
def diagonalPullbackHom (Q : Subgroup E) :
    D (aG.comp Q.subtype) (aL.comp Q.subtype) →*
      (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E :=
  (subgroupSemidirectEmbedding aG aL Q).comp
    (inverseHom (aG.comp Q.subtype) (aL.comp Q.subtype))

@[simp] theorem diagonalPullbackHom_base (Q : Subgroup E) (x : G × Lᵐᵒᵖ) :
    diagonalPullbackHom aG aL Q
        (baseEmbedding (aG.comp Q.subtype) (aL.comp Q.subtype) x) =
      SemidirectProduct.inl x := by
  simp only [diagonalPullbackHom, MonoidHom.comp_apply, inverseHom_base,
    subgroupSemidirectEmbedding_inl]

@[simp] theorem diagonalPullbackHom_field (Q : Subgroup E) (q : Q) :
    diagonalPullbackHom aG aL Q
        (fieldEmbedding (aG.comp Q.subtype) (aL.comp Q.subtype) q) =
      SemidirectProduct.inr q.val := by
  simp only [diagonalPullbackHom, MonoidHom.comp_apply, inverseHom_field,
    subgroupSemidirectEmbedding_inr]

theorem diagonalPullbackHom_comp_base (Q : Subgroup E) :
    (diagonalPullbackHom aG aL Q).comp
        (baseEmbedding (aG.comp Q.subtype) (aL.comp Q.subtype)) =
      (SemidirectProduct.inl : G × Lᵐᵒᵖ →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) := by
  apply MonoidHom.ext
  exact diagonalPullbackHom_base aG aL Q

/-- An honest representation remains on the same vector space after restriction. -/
def diagonalRepresentation (Q : Subgroup E)
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) V) :
    Representation k (D (aG.comp Q.subtype) (aL.comp Q.subtype)) V :=
  rho.comp (diagonalPullbackHom aG aL Q)

@[simp] theorem diagonalRepresentation_base (Q : Subgroup E)
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) V)
    (x : G × Lᵐᵒᵖ) (v : V) :
    diagonalRepresentation aG aL Q rho
        (baseEmbedding (aG.comp Q.subtype) (aL.comp Q.subtype) x) v =
      rho (SemidirectProduct.inl x) v := by
  simp only [diagonalRepresentation, MonoidHom.comp_apply, diagonalPullbackHom_base]

@[simp] theorem diagonalRepresentation_field (Q : Subgroup E)
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) V)
    (q : Q) (v : V) :
    diagonalRepresentation aG aL Q rho
        (fieldEmbedding (aG.comp Q.subtype) (aL.comp Q.subtype) q) v =
      rho (SemidirectProduct.inr q.val) v := by
  simp only [diagonalRepresentation, MonoidHom.comp_apply, diagonalPullbackHom_field]

/-- Restriction to the base is canonically the restriction of the same honest action. -/
def diagonalBaseIso (Q : Subgroup E)
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) V) :
    Rep.res (baseEmbedding (aG.comp Q.subtype) (aL.comp Q.subtype))
        (Rep.of (diagonalRepresentation aG aL Q rho)) ≅
      Rep.res (SemidirectProduct.inl : G × Lᵐᵒᵖ →*
        (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) (Rep.of rho) :=
  eqToIso (congrArg (fun f => Rep.of (rho.comp f))
    (diagonalPullbackHom_comp_base aG aL Q))

/-- The induced bimodule is this exact installed induction expression. -/
def inducedModule (Q : Subgroup E)
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) V) :
    Rep k ((G ⋊[aG.comp Q.subtype] Q) × (L ⋊[aL.comp Q.subtype] Q)ᵐᵒᵖ) :=
  Rep.ind (D (aG.comp Q.subtype) (aL.comp Q.subtype)).subtype
    (Rep.of (diagonalRepresentation aG aL Q rho))

/-- This model uses inverse right translation on its induction generators. -/
theorem inducedModule_mk (Q : Subgroup E)
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) V)
    (h₁ h₂ : (G ⋊[aG.comp Q.subtype] Q) × (L ⋊[aL.comp Q.subtype] Q)ᵐᵒᵖ)
    (v : V) :
    (inducedModule aG aL Q rho).ρ h₁
        (Representation.IndV.mk _ (diagonalRepresentation aG aL Q rho) h₂ v) =
      Representation.IndV.mk _ (diagonalRepresentation aG aL Q rho) (h₂ * h₁⁻¹) v :=
  Representation.ind_mk _ _ h₁ h₂ v

end ModularRep.PaperProofs.TypeBRankThreeMoritaInduced


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
