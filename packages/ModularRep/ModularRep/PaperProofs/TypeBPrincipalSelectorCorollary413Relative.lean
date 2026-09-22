import ModularRep.ProjectiveBrauerDuality
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Paper proof: field fixation from the GGGR projective basis

This file checks the linear-algebra and duality deduction in manuscript
Corollary 4.10.  The input is the basis of principal-block projective
characters constructed in Proposition 4.9, together with its pointwise
field fixation from Lemma 4.7.  Lean first proves that the resulting linear
action fixes the entire projective character space, then fixes the projective
indecomposable basis and finally transfers fixation to irreducible Brauer
characters through the standard equivariant dual indexing.

The file does not construct generalised Gelfand--Graev characters, projective
indecomposable characters, or the projective--Brauer pairing.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413Relative

open ModularRep.ManuscriptVerification.ProjectiveBrauerDuality
open Module

universe uK uV uI uE uP uB

variable {K : Type uK} {V : Type uV} {I : Type uI}
variable {E : Type uE} {Projective : Type uP} {Brauer : Type uB}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Group E] [MulAction E Projective] [MulAction E Brauer]

/-- A linear automorphism that fixes every vector of a basis fixes every
vector in the space. -/
theorem linear_action_fixed_of_basis_fixed
    (rho : E →* (V ≃ₗ[K] V)) (B : Basis I K V)
    (basis_fixed : ∀ e : E, ∀ i : I, rho e (B i) = B i) :
    ∀ e : E, ∀ v : V, rho e v = v := by
  intro e v
  have hmap : (rho e).toLinearMap = LinearMap.id := by
    exact B.ext (basis_fixed e)
  exact LinearMap.congr_fun hmap v

/-- The exact linear-algebra deduction used in Corollary 4.10.
No pointwise fixation of the whole projective character space or of the
projective indecomposable labels is assumed. -/
theorem brauer_fixed_from_gggr_projective_basis
    (rho : E →* (V ≃ₗ[K] V))
    (gggrBasis : Basis I K V)
    (gggrBasis_fixed : ∀ e : E, ∀ i : I,
      rho e (gggrBasis i) = gggrBasis i)
    (projectiveCharacter : Projective → V)
    (projectiveCharacter_injective : Function.Injective projectiveCharacter)
    (projectiveCharacter_equivariant : ∀ e : E, ∀ P : Projective,
      projectiveCharacter (e • P) = rho e (projectiveCharacter P))
    (duality : EquivariantDualIndexing (E := E)
      (Projective := Projective) (Brauer := Brauer)) :
    ∀ e : E, ∀ phi : Brauer, e • phi = phi := by
  apply brauer_fixed_of_projective_fixed duality
  intro e P
  apply projectiveCharacter_injective
  rw [projectiveCharacter_equivariant]
  exact linear_action_fixed_of_basis_fixed rho gggrBasis gggrBasis_fixed e
    (projectiveCharacter P)

end ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
