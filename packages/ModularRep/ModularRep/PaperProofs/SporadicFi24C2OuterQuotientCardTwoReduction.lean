import ModularRep.PaperProofs.SporadicFi24C2OuterActionSourceReduction

/-!
# Cardinality-two construction of the Fischer outer quotient binding

This experimental module constructs the three-field
`Fi24C2OuterQuotientBinding` from a lower-level pair of structural facts.  The
literal subgroup is the range of `RepresentationWeight.innerInverseOpHom`;
its normality is proved in K from naturality of inner automorphisms.  A
cardinality-two identification of the quotient then gives, in K, its regular
permutation action on `Fin 2`, whose kernel is exactly the inner range.

The ordered two-field source is graded E1/U: it records only that the literal
quotient by the inner range has cardinality two and that the selected
automorphism supplied by `S` is not inner.  The record is generic in `X` and
is intended for a separately verified concrete Fischer instantiation; it is
not itself a proof that `Out(Fi'_24)` is isomorphic to `C2`.  It supplies no
permutation homomorphism, kernel equality, carrier action, carrier-fixation
clause, character--weight map, fibre equivalence, raw sector family, orbit
census, An--Dietrich input, Spath input, Proposition 5.7 conclusion,
BAW-goodness, or iBAW conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24C2OuterQuotientCardTwoReduction

open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24C2OuterActionSourceReduction

universe u

variable {k X : Type u}
variable [Field k] [Group X] [Fintype X]

/-- The range of the literal inner-automorphism homomorphism is normal in the
opposite automorphism group.  This is a K theorem: conjugating the inner
automorphism represented by `x` by `alpha` gives the inner automorphism
represented by `alpha.unop⁻¹ x`. -/
private theorem innerInverseOpRange_normal :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.Normal := by
  constructor
  intro beta hbeta alpha
  rcases hbeta with ⟨x, rfl⟩
  refine ⟨(alpha.unop⁻¹) x, ?_⟩
  apply MulOpposite.unop_injective
  ext y
  simp [RepresentationWeight.innerInverseOpHom, mul_assoc]

local instance innerInverseOpRangeNormal :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.Normal :=
  innerInverseOpRange_normal

noncomputable local instance mulAutFinite : Finite (MulAut X) :=
  Finite.of_injective (fun alpha : MulAut X ↦ (alpha : X → X))
    DFunLike.coe_injective

noncomputable local instance mulAutOpFinite : Finite (MulAut X)ᵐᵒᵖ :=
  Finite.of_equiv (MulAut X) MulOpposite.opEquiv

noncomputable local instance outerQuotientFinite :
    Finite
      ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range) :=
  Finite.of_surjective
    (QuotientGroup.mk'
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (QuotientGroup.mk'_surjective
      (RepresentationWeight.innerInverseOpHom (G := X)).range)

/-- The exact E1/U facts needed to recover a two-point outer action for the
intended concrete instantiation.  No action or kernel identification is
stored in this generic source. -/
structure Fi24C2OuterQuotientCardTwoSource
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Prop where
  quotient_card_two :
    Nat.card
      ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2
  selectedOuter_not_inner :
    S.outer ∉
      (RepresentationWeight.innerInverseOpHom (G := X)).range

/-- A noncanonical labelling of the literal outer quotient by `Fin 2`,
obtained solely from the supplied cardinality equality. -/
private noncomputable def outerQuotientEquivFinTwo
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Fi24C2OuterQuotientCardTwoSource S) :
    ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) ≃ Fin 2 :=
  Finite.equivFinOfCardEq Q.quotient_card_two

/-- The faithful regular action of the quotient, transported to `Fin 2`. -/
private noncomputable def outerQuotientFinTwoAction
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Fi24C2OuterQuotientCardTwoSource S) :
    (((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range) →*
      Equiv.Perm (Fin 2)) :=
  (outerQuotientEquivFinTwo S Q).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom
      ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range)
      ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range))

private theorem outerQuotientFinTwoAction_injective
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Fi24C2OuterQuotientCardTwoSource S) :
    Function.Injective (outerQuotientFinTwoAction S Q) :=
  (outerQuotientEquivFinTwo S Q).permCongrHom.injective.comp
    MulAction.toPerm_injective

/-- The derived action of the opposite automorphism group on the two
labelled quotient classes. -/
private noncomputable def outerClassOfCardTwo
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Fi24C2OuterQuotientCardTwoSource S) :
    (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2) :=
  (outerQuotientFinTwoAction S Q).comp
    (QuotientGroup.mk'
      (RepresentationWeight.innerInverseOpHom (G := X)).range)

private theorem outerClassOfCardTwo_ker
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Fi24C2OuterQuotientCardTwoSource S) :
    (outerClassOfCardTwo S Q).ker =
      (RepresentationWeight.innerInverseOpHom (G := X)).range := by
  unfold outerClassOfCardTwo
  calc
    ((outerQuotientFinTwoAction S Q).comp
        (QuotientGroup.mk'
          (RepresentationWeight.innerInverseOpHom (G := X)).range)).ker =
        (QuotientGroup.mk'
          (RepresentationWeight.innerInverseOpHom (G := X)).range).ker :=
      MonoidHom.ker_comp_of_injective _ _
        (outerQuotientFinTwoAction_injective S Q)
    _ = (RepresentationWeight.innerInverseOpHom (G := X)).range :=
      QuotientGroup.ker_mk'
        (RepresentationWeight.innerInverseOpHom (G := X)).range

private theorem outerClassOfCardTwo_selectedOuter_nontrivial
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Fi24C2OuterQuotientCardTwoSource S) :
    outerClassOfCardTwo S Q S.outer ≠ 1 := by
  intro houter
  apply Q.selectedOuter_not_inner
  have hker : S.outer ∈ (outerClassOfCardTwo S Q).ker := houter
  rwa [outerClassOfCardTwo_ker S Q] at hker

/-- Construct the existing structural outer-quotient binding from the two
cardinality/non-inner source facts.  The quotient action, its nontrivial
selected class, and its exact kernel are all K deductions. -/
noncomputable def fi24C2OuterQuotientBinding_ofCardTwo
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Fi24C2OuterQuotientCardTwoSource S) :
    Fi24C2OuterQuotientBinding S where
  outerClass := outerClassOfCardTwo S Q
  selectedOuter_nontrivial :=
    outerClassOfCardTwo_selectedOuter_nontrivial S Q
  kernel_eq_inner := outerClassOfCardTwo_ker S Q

end ModularRep.PaperProofs.SporadicFi24C2OuterQuotientCardTwoReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
