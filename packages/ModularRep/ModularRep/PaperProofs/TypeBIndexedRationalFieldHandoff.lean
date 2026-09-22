import ModularRep.PaperProofs.TypeBLemma411Proposition412LiteralHandoff

/-!
# The rational-class handoff indexed by geometric unipotent class

Malle--Testerman's rational-class parametrisation is applied separately
inside each geometric class. The component group, inner automorphism
element and rational-class fibre may therefore depend on that class.
Every index of the SAME literal GGGR family has a geometric label and a
rational class in that dependent fibre, with an exact function equality.

The checked inner twisted-conjugacy deduction is reused fibre by fibre.
Taylor's action is converted by the existing exact inverse-pullback
identity before the resulting full-GGGR fixation is passed to the checked
Proposition 4.9/Corollary 4.10 bridge. No common parameter space for the
union of geometric classes, GGGR/Brauer fixation, basis or target predicate
is a source field. Literal algebraic-group and source realization remains
an explicit application obligation.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBIndexedRationalFieldHandoff

open ModularRep
open TypeBRationalFieldLemma411Relative
open TypeBGGGRRankProposition412SourceInstantiation
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBGGGRRankProposition412Corollary413Bridge
open TypeBLemma411Proposition412LiteralHandoff

universe u

variable {p n : Nat} {k K G E GeometricClass : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G] [CommGroup E]
  {projectiveSpace : Submodule K (G → K)}
  [FiniteDimensional K projectiveSpace]

/-- Source-sized data on individual geometric classes. The dependent
rational representative binds each literal GGGR index to one specified
class; no equivalence of all classes with one component group is assumed. -/
structure IndexedLiteralLemma411Source
    (ComponentGroup : GeometricClass → Type u)
    (RationalClass : GeometricClass → Type u)
    [∀ C, Group (ComponentGroup C)]
    [∀ C, MulAction E (RationalClass C)]
    (field : E →* (MulAut G)ᵐᵒᵖ)
    (D : GGGRBasisSource n projectiveSpace)
    (inner : ∀ C, ComponentGroup C) (f : Nat) where
  parameter : ∀ C, RationalClassParametrisation
    (E := E) (RationalClass := RationalClass C) (inner C) f
  gamma : ∀ C, RationalClass C → G → K
  taylorEquivariant :
    let _ : MulAction E (G → K) := taylorFunctionFieldAction field
    ∀ (C : GeometricClass) (e : E) (r : RationalClass C),
      e • gamma C r = gamma C (e • r)
  geometricClassOfIndex : Fin n → GeometricClass
  rationalClassOfIndex : ∀ j : Fin n, RationalClass (geometricClassOfIndex j)
  gggr_eq_gamma : ∀ j : Fin n,
    D.gggr j = gamma (geometricClassOfIndex j) (rationalClassOfIndex j)

namespace IndexedLiteralLemma411Source

variable {ComponentGroup RationalClass : GeometricClass → Type u}
  [∀ C, Group (ComponentGroup C)]
  [∀ C, MulAction E (RationalClass C)]
  {field : E →* (MulAut G)ᵐᵒᵖ}
  {D : GGGRBasisSource n projectiveSpace}
  {inner : ∀ C, ComponentGroup C} {f : Nat}

/-- Rational-class fixation is derived separately in each geometric class. -/
theorem rationalClass_fixed
    (S : IndexedLiteralLemma411Source ComponentGroup RationalClass field D inner f)
    (C : GeometricClass) (e : E) (r : RationalClass C) :
    e • r = r :=
  (S.parameter C).smul_eq_self e r

/-- The checked Lemma 4.7 deduction is applied in precisely the component
group belonging to C. The result uses the existing literal function twist. -/
theorem gamma_fixed
    (S : IndexedLiteralLemma411Source ComponentGroup RationalClass field D inner f)
    (C : GeometricClass) (e : E) (r : RationalClass C) :
    functionTwistLinearEquiv (K := K) (field e).unop (S.gamma C r) =
      S.gamma C r := by
  let _ : MulAction E (G → K) := taylorFunctionFieldAction field
  have fixed := lemma_4_11_relative (S.parameter C) (S.gamma C) (S.taylorEquivariant C)
  rw [← manuscriptRightAction_eq_functionTwist (K := K) field]
  exact fixed.2 e r

/-- The SAME full GGGR family used by the Proposition 4.9 source is
fixed, because each index is bound to its own geometric/rational class. -/
theorem gggr_fixed
    (S : IndexedLiteralLemma411Source ComponentGroup RationalClass field D inner f) :
    ∀ e : E, ∀ j : Fin n,
      functionTwistLinearEquiv (K := K) (field e).unop (D.gggr j) = D.gggr j := by
  intro e j
  rw [S.gggr_eq_gamma j]
  exact S.gamma_fixed (S.geometricClassOfIndex j) e (S.rationalClassOfIndex j)

/-- Indexed source handoff to the existing constructed-basis/projective
formula proof. No fixedness or independently supplied basis is a premise. -/
theorem corollary_4_13_from_indexed_literal_lemma_4_11
    (S : IndexedLiteralLemma411Source ComponentGroup RationalClass field D inner f)
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
    iota inPrincipalBlock brauerStable projectiveStable B S.gggr_fixed

end IndexedLiteralLemma411Source

end ModularRep.PaperProofs.TypeBIndexedRationalFieldHandoff



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
