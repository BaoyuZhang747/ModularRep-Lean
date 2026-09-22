import ModularRep.BrauerCharacterKZero
import ModularRep.OrdinaryCharacterKZero
import ModularRep.Twist
import Mathlib.CategoryTheory.Action.Limits

/-!
# Automorphism twists on exact Grothendieck groups

Twisting a finite dimensional representation by a group automorphism is an
exact autoequivalence.  This file constructs the induced automorphism of the
exact Grothendieck group and proves that both ordinary and Brauer character
homomorphisms commute with it.

These are formal consequences of the definitions.  No character-theoretic
equivariance statement is assumed.
-/

noncomputable section

open CategoryTheory

namespace ModularRep

universe u

namespace FDRep

variable (k : Type u) (G : Type u) [Field k] [Group G]

/-- Twisting finite dimensional representations by a group automorphism. -/
noncomputable def twistEquivalence (alpha : MulAut G) :
    FDRep k G ≌ FDRep k G :=
  Action.resEquiv (FGModuleCat k) alpha

@[simp]
theorem twistEquivalence_obj_rho (alpha : MulAut G) (V : FDRep k G) :
    ((twistEquivalence k G alpha).functor.obj V).ρ =
      Representation.twist V.ρ alpha :=
  rfl

@[simp]
theorem twistEquivalence_obj_regularTraceClassFunction
    (p : ℕ) (alpha : MulAut G) (V : FDRep k G) :
    Representation.regularTraceClassFunction
        (((twistEquivalence k G alpha).functor.obj V).ρ) p =
      (Representation.regularTraceClassFunction V.ρ p).twist alpha := by
  ext g
  rfl

variable {p : ℕ} {K : Type u} [Field K] [Finite G]
  [CharP k p] [IsAlgClosed k] [CharZero K]

@[simp]
theorem twistEquivalence_obj_brauerCharacter
    (iota : PrimeRegularRootEmbedding p k K G)
    (alpha : MulAut G) (V : FDRep k G) :
    Representation.brauerCharacterOfRootEmbedding
        (((twistEquivalence k G alpha).functor.obj V).ρ) iota =
      (Representation.brauerCharacterOfRootEmbedding V.ρ iota).twist alpha := by
  ext g
  rfl

end FDRep

open ExactGrothendieckGroup
open FDRepSimpleClassKZero

variable {k G : Type u} [Field k] [Group G]

/-- The automorphism twist induced on the exact Grothendieck group. -/
noncomputable def twistKZero (alpha : MulAut G) :
    FDRepKZero k G →+ FDRepKZero k G :=
  ExactGrothendieckGroup.map (FDRep.twistEquivalence k G alpha).functor

@[simp]
theorem twistKZero_classOf (alpha : MulAut G) (V : FDRep k G) :
    twistKZero (k := k) alpha (classOf (FDRep k G) V) =
      classOf (FDRep k G)
        ((FDRep.twistEquivalence k G alpha).functor.obj V) :=
  ExactGrothendieckGroup.map_classOf
    (FDRep.twistEquivalence k G alpha).functor V

/-- Twisting by the identity automorphism induces the identity on exact
`K₀`. -/
theorem twistKZero_refl :
    twistKZero (k := k) (MulEquiv.refl G) =
      AddMonoidHom.id (FDRepKZero k G) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [twistKZero_classOf]
  rfl

/-- Successive exact-`K₀` twists obey the right-action composition law. -/
theorem twistKZero_comp (alpha beta : MulAut G) :
    (twistKZero (k := k) alpha).comp (twistKZero (k := k) beta) =
      twistKZero (k := k) (beta * alpha) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, twistKZero_classOf,
    twistKZero_classOf, twistKZero_classOf]
  rfl

/-- The right action by automorphism twists, represented as a left action of
the opposite automorphism group on exact `K₀`. -/
noncomputable def twistKZeroRepresentation :
    Representation ℤ (MulAut G)ᵐᵒᵖ (FDRepKZero k G) where
  toFun alpha := (twistKZero (k := k) alpha.unop).toIntLinearMap
  map_one' := by
    apply LinearMap.toAddMonoidHom_injective
    exact twistKZero_refl (k := k) (G := G)
  map_mul' alpha beta := by
    apply LinearMap.toAddMonoidHom_injective
    exact (twistKZero_comp (k := k) (G := G)
      alpha.unop beta.unop).symm

@[simp]
theorem twistKZeroRepresentation_apply
    (alpha : (MulAut G)ᵐᵒᵖ) (x : FDRepKZero k G) :
    twistKZeroRepresentation (k := k) (G := G) alpha x =
      twistKZero (k := k) alpha.unop x :=
  rfl

namespace PrimeRegularClassFunction

variable {p : ℕ} {K : Type u} [Field K]

/-- Pullback by a group automorphism as an additive equivalence of class
functions. -/
def twistAddEquiv (alpha : MulAut G) :
    PrimeRegularClassFunction K G p ≃+ PrimeRegularClassFunction K G p where
  toFun f := f.twist alpha
  invFun f := f.twist alpha.symm
  left_inv f := by
    change (f.twist alpha).twist alpha.symm = f
    rw [PrimeRegularClassFunction.twist_mul]
    have h : alpha * alpha.symm = MulEquiv.refl G := by
      ext g
      simp
    rw [h, PrimeRegularClassFunction.twist_refl]
  right_inv f := by
    change (f.twist alpha.symm).twist alpha = f
    rw [PrimeRegularClassFunction.twist_mul]
    have h : alpha.symm * alpha = MulEquiv.refl G := by
      ext g
      simp
    rw [h, PrimeRegularClassFunction.twist_refl]
  map_add' f h := by
    ext x
    rfl

end PrimeRegularClassFunction

variable {p : ℕ} {K : Type u} [Field K]

/-- The ordinary-character homomorphism on exact `K₀` commutes with
automorphism twists. -/
theorem ordinaryCharacterKZero_twist (alpha : MulAut G) :
    (ordinaryCharacterKZero (K := K) (G := G) p).comp
        (twistKZero (k := K) alpha) =
      (PrimeRegularClassFunction.twistAddEquiv
        (p := p) (K := K) alpha).toAddMonoidHom.comp
        (ordinaryCharacterKZero (K := K) (G := G) p) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, twistKZero_classOf,
    ordinaryCharacterKZero_classOf, AddMonoidHom.comp_apply,
    ordinaryCharacterKZero_classOf]
  rw [FDRep.twistEquivalence_obj_regularTraceClassFunction]
  rfl

variable [Finite G] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The Brauer-character homomorphism on exact `K₀` commutes with
automorphism twists. -/
theorem brauerCharacterKZeroHom_twist
    (iota : PrimeRegularRootEmbedding p k K G) (alpha : MulAut G) :
    (brauerCharacterKZeroHom iota).comp (twistKZero (k := k) alpha) =
      (PrimeRegularClassFunction.twistAddEquiv
        (p := p) (K := K) alpha).toAddMonoidHom.comp
        (brauerCharacterKZeroHom iota) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, twistKZero_classOf,
    brauerCharacterKZeroHom_classOf, AddMonoidHom.comp_apply,
    brauerCharacterKZeroHom_classOf]
  rw [FDRep.twistEquivalence_obj_brauerCharacter]
  rfl

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
