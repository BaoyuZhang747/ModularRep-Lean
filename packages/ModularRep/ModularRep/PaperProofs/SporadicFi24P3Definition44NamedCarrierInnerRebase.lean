import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness

/-!
# Inner change of the base embedding

The ambient group, base subgroup and centre remain the same. Composing the
base embedding with an inner automorphism changes its conjugation formula
and stabilizer identification by the corresponding inner conjugation.
No additional character or group source is required.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInnerRebase

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

universe u

variable {P : Definition35Problem.{u}}
variable {reference psi : Definition35Brauer P}
variable {quotient : CentralQuotientBrauerSource P reference psi}

def innerActor (g : CentralCharacterQuotient P reference) :
    QuotientBrauerAutomorphismStabilizer P reference psi quotient := by
  refine ⟨MulOpposite.op (MulAut.conj g), ?_⟩
  apply Subtype.ext
  change quotient.brauer.1.twist (MulAut.conj g) = quotient.brauer.1
  exact PrimeRegularClassFunction.twist_conj quotient.brauer.1 g

def innerRebase (ambient : SpathAmbientGroup P reference psi quotient)
    (g : CentralCharacterQuotient P reference) :
    SpathAmbientGroup P reference psi quotient where
  A := ambient.A
  groupA := ambient.groupA
  fintypeA := ambient.fintypeA
  base := ambient.base
  baseNormal := ambient.baseNormal
  baseEquiv := (MulAut.conj g).trans ambient.baseEquiv
  baseCentralizer_eq_center := ambient.baseCentralizer_eq_center
  centerPrimeTo := ambient.centerPrimeTo
  conjugation := (MulAut.congr (MulAut.conj g).symm).toMonoidHom.comp ambient.conjugation
  conjugation_on_base a h := by
    change (ambient.baseEquiv ((MulAut.conj g)
      ((MulAut.conj g).symm (ambient.conjugation a ((MulAut.conj g) h)))) : ambient.A) =
      a * (ambient.baseEquiv ((MulAut.conj g) h) : ambient.A) * a⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact ambient.conjugation_on_base a ((MulAut.conj g) h)
  automorphismQuotientEquiv := ambient.automorphismQuotientEquiv.trans
    (MulAut.conj (innerActor (quotient := quotient) g))
  automorphismQuotientEquiv_natural a := by
    apply MulOpposite.unop_injective
    apply DFunLike.ext
    intro x
    change (MulAut.conj g).symm
      (((ambient.automorphismQuotientEquiv
        (QuotientGroup.mk' (Subgroup.center ambient.A) a)).1).unop ((MulAut.conj g) x)) =
      (MulAut.conj g).symm (ambient.conjugation a⁻¹ ((MulAut.conj g) x))
    exact congrArg
      (fun z : (MulAut (CentralCharacterQuotient P reference))ᵐᵒᵖ =>
        (MulAut.conj g).symm (z.unop ((MulAut.conj g) x)))
      (ambient.automorphismQuotientEquiv_natural a)

theorem innerRebase_base (ambient : SpathAmbientGroup P reference psi quotient)
    (g : CentralCharacterQuotient P reference) :
    (innerRebase ambient g).base = ambient.base := rfl

theorem quotientToAmbient_innerRebase
    (ambient : SpathAmbientGroup P reference psi quotient)
    (g : CentralCharacterQuotient P reference) :
    quotientToAmbient P reference psi quotient (innerRebase ambient g) =
      (quotientToAmbient P reference psi quotient ambient).comp
        (MulAut.conj g).toMonoidHom := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInnerRebase


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
