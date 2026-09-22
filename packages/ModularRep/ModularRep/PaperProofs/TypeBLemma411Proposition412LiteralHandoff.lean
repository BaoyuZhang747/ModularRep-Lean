import ModularRep.PaperProofs.TypeBRationalFieldLemma411Relative
import ModularRep.PaperProofs.TypeBGGGRRankProposition412Corollary413Bridge

/-!
# Literal Lemma 4.7 to Proposition 4.9 and Corollary 4.10 handoff

This file removes full-GGGR fixedness as a free input at the handoff from
Lemma 4.7 to Proposition 4.9 and Corollary 4.10.  The field group acts on
literal functions `G → K` by pullback.  The manuscript writes this as a
right action, so its automorphism map has target `(MulAut G)ᵐᵒᵖ`.
Taylor's left action is the inverse pullback action.  Lean checks that
Taylor's convention, the manuscript's convention, and the literal function
action used by the Proposition 4.9 bridge coincide with the required
inverses.

The rational-class parametrisation and Taylor's equivariance theorem remain
exact source inputs.  The matching of the GGGR indexed by a rational class
with the literal GGGR in `GGGRBasisSource` is an explicit carrier adapter.
There is no GGGR-fixedness, basis, projected-component fixedness, Brauer
fixedness, BAW, or iBAW field.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLemma411Proposition412LiteralHandoff

open ModularRep.PaperProofs.TypeBRationalFieldLemma411Relative
open ModularRep.PaperProofs.TypeBGGGRRankProposition412SourceInstantiation
open ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413SourceInstantiation
open ModularRep.PaperProofs.TypeBGGGRRankProposition412Corollary413Bridge

universe u

variable {p n : Nat} {k K G E A RationalClass : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [CommGroup E] [Group A]
variable [MulAction E RationalClass]
variable {projectiveSpace : Submodule K (G → K)}
variable [FiniteDimensional K projectiveSpace]

/-! ## Exact action conversion -/

/-- Taylor's left action on literal class functions.  If `alpha_e` is the
automorphism represented by `e`, this action sends `chi` to
`chi ∘ alpha_e⁻¹`.  Commutativity is available because the field group in
the manuscript is cyclic. -/
@[instance_reducible] def taylorFunctionFieldAction
    (field : E →* (MulAut G)ᵐᵒᵖ) : MulAction E (G → K) :=
  MulAction.compHom (G → K)
    ((functionFieldRepresentation (K := K) field).comp invMonoidHom)

@[simp]
theorem taylorFunctionFieldAction_apply
    (field : E →* (MulAut G)ᵐᵒᵖ) (e : E) (chi : G → K) (g : G) :
    let _ : MulAction E (G → K) := taylorFunctionFieldAction field
    (e • chi) g = chi ((field e⁻¹).unop g) := by
  rfl

/-- Inverting Taylor's left action gives exactly the literal pullback used
for the manuscript's right action and for Corollary 4.10. -/
theorem manuscriptRightAction_eq_functionTwist
    (field : E →* (MulAut G)ᵐᵒᵖ) (e : E) (chi : G → K) :
    let _ : MulAction E (G → K) := taylorFunctionFieldAction field
    manuscriptRightAction e chi =
      functionTwistLinearEquiv (K := K) (field e).unop chi := by
  funext g
  change chi ((field (e⁻¹)⁻¹).unop g) = chi ((field e).unop g)
  simp

/-! ## Literal source interface -/

/-- Source-shaped data matching Lemma 4.7 to the literal GGGR carrier used
in Proposition 4.9.

`parameter` and `taylorEquivariant` are respectively the rational-class
parametrisation and Taylor's GGGR equivariance theorem.  `gggr_eq_gamma`
only identifies two constructions of the same literal GGGR.  None of the
fields asserts any fixedness conclusion. -/
structure LiteralLemma411Source
    (field : E →* (MulAut G)ᵐᵒᵖ)
    (D : GGGRBasisSource n projectiveSpace)
    (c : A) (f : Nat) where
  parameter : RationalClassParametrisation
    (E := E) (RationalClass := RationalClass) c f
  gamma : RationalClass → G → K
  taylorEquivariant :
    let _ : MulAction E (G → K) := taylorFunctionFieldAction field
    ∀ (e : E) (r : RationalClass), e • gamma r = gamma (e • r)
  rationalClassOfIndex : Fin n → RationalClass
  gggr_eq_gamma : ∀ j : Fin n, D.gggr j = gamma (rationalClassOfIndex j)

namespace LiteralLemma411Source

variable {field : E →* (MulAut G)ᵐᵒᵖ}
variable {D : GGGRBasisSource n projectiveSpace}
variable {c : A} {f : Nat}

/-- Lemma 4.7 now fixes the same literal full GGGRs used by Proposition
4.9.  Fixedness is derived, not supplied by the source interface. -/
theorem gggr_fixed
    (S : LiteralLemma411Source
      (RationalClass := RationalClass) field D c f) :
    ∀ e : E, ∀ j : Fin n,
      functionTwistLinearEquiv (K := K) (field e).unop (D.gggr j) =
        D.gggr j := by
  let _ : MulAction E (G → K) := taylorFunctionFieldAction field
  have h := lemma_4_11_relative S.parameter S.gamma S.taylorEquivariant
  intro e j
  rw [S.gggr_eq_gamma]
  rw [← manuscriptRightAction_eq_functionTwist (K := K) field]
  exact h.2 e (S.rationalClassOfIndex j)

/-- End-to-end literal handoff from the source-shaped Lemma 4.7 inputs,
through the basis constructed in Proposition 4.9, to the actual Brauer
characters of Corollary 4.10.  Full-GGGR fixedness is no longer a premise. -/
theorem corollary_4_13_from_literal_lemma_4_11
    (S : LiteralLemma411Source
      (RationalClass := RationalClass) field D c f)
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (brauerStable : ∀ e : E, ∀ phi : IBr iota,
      inPrincipalBlock phi →
        inPrincipalBlock
          (IrreducibleBrauerCharacter.twist iota phi (field e).unop))
    (projectiveStable : ∀ e : E, ∀ q : G → K, q ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop q ∈ projectiveSpace)
    (B : ProjectiveBrauerFormulaSource field iota inPrincipalBlock
      brauerStable projectiveSpace projectiveStable)
    (P : PrincipalProjectionFieldSource field D) :
    let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
    ∀ e : E, ∀ phi : PrincipalBrauerCarrier iota inPrincipalBlock,
      e • phi = phi := by
  exact P.corollary_4_13_of_proposition_4_12_and_lemma_4_11
    iota inPrincipalBlock brauerStable projectiveStable B (S.gggr_fixed)

end LiteralLemma411Source

end ModularRep.PaperProofs.TypeBLemma411Proposition412LiteralHandoff


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
