import ModularRep.PaperProofs.TypeBGGGRRankProposition412SourceInstantiation
import ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413SourceInstantiation

/-!
# Direct Proposition 4.9 to Corollary 4.10 bridge

This file closes the literal-carrier handoff between the two results.  The
input from Lemma 4.7 is fixation of each full, function-valued GGGR.  The
only new source adapter is the standard naturality of the literal
principal-block projection under field automorphisms.  Lean derives fixation
of every projected GGGR component and then of the basis constructed by
Proposition 4.9.  No basis or basis-fixedness assertion is an input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBGGGRRankProposition412Corollary413Bridge

open Module
open ModularRep.PaperProofs.TypeBGGGRRankProposition412SourceInstantiation
open ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413SourceInstantiation

universe u

variable {p n : Nat} {k K G E : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group E]
variable {projectiveSpace : Submodule K (G → K)}
variable [FiniteDimensional K projectiveSpace]

/-- Universe-lifted finite index used only to meet Corollary 4.10's
single-universe carrier signature. -/
abbrev CorollaryIndex (n : Nat) := ULift.{u} (Fin n)

/-- Exact E1/U adapter asserting that the literal principal-block projection
commutes with the specified literal field pullback.  It does not assert that
any GGGR, projected component, basis vector, projective character, or Brauer
character is fixed. -/
structure PrincipalProjectionFieldSource
    (field : E →* (MulAut G)ᵐᵒᵖ)
    (D : GGGRBasisSource n projectiveSpace) where
  principalProjection_natural : ∀ e : E, ∀ f : G → K,
    functionTwistLinearEquiv (K := K) (field e).unop
        (D.principalProjection f) =
      D.principalProjection
        (functionTwistLinearEquiv (K := K) (field e).unop f)

namespace PrincipalProjectionFieldSource

variable {field : E →* (MulAut G)ᵐᵒᵖ}
variable {D : GGGRBasisSource n projectiveSpace}

/-- Literal fixation of each full GGGR and naturality of block projection
force fixation of each actual principal-block GGGR component. -/
theorem principalGGGRComponent_fixed
    (P : PrincipalProjectionFieldSource field D)
    (projectiveStable : ∀ e : E, ∀ f : G → K, f ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace)
    (gggr_fixed : ∀ e : E, ∀ j : Fin n,
      functionTwistLinearEquiv (K := K) (field e).unop (D.gggr j) =
        D.gggr j) :
    ∀ e : E, ∀ j : Fin n,
      projectiveFieldRepresentation field projectiveSpace
          projectiveStable e (D.principalGGGRComponent j) =
        D.principalGGGRComponent j := by
  intro e j
  apply Subtype.ext
  change functionTwistLinearEquiv (K := K) (field e).unop
      (D.principalProjection (D.gggr j)) =
    D.principalProjection (D.gggr j)
  rw [P.principalProjection_natural, gggr_fixed]

/-- The basis used by Corollary 4.10 is the basis derived in Proposition
4.9, so component fixation gives basis-vector fixation without a basis-fixed
premise. -/
theorem gggrProjectiveBasis_fixed
    (P : PrincipalProjectionFieldSource field D)
    (projectiveStable : ∀ e : E, ∀ f : G → K, f ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace)
    (gggr_fixed : ∀ e : E, ∀ j : Fin n,
      functionTwistLinearEquiv (K := K) (field e).unop (D.gggr j) =
        D.gggr j) :
    ∀ e : E, ∀ j : Fin n,
      projectiveFieldRepresentation field projectiveSpace
          projectiveStable e (D.gggrProjectiveBasis j) =
        D.gggrProjectiveBasis j := by
  intro e j
  have hcoe : D.gggrProjectiveBasis j = D.principalGGGRComponent j :=
    congrFun D.coe_gggrProjectiveBasis j
  rw [hcoe]
  exact P.principalGGGRComponent_fixed projectiveStable gggr_fixed e j

/-- Reindex the derived Proposition 4.9 basis into Corollary 4.10's carrier
universe.  This changes labels only, not basis vectors. -/
def corollaryGGGRBasis (D : GGGRBasisSource n projectiveSpace) :
    Basis (CorollaryIndex.{u} n) K projectiveSpace :=
  D.gggrProjectiveBasis.reindex Equiv.ulift.symm

/-- The reindexed basis remains fixed because its vectors are precisely the
derived GGGR components. -/
theorem corollaryGGGRBasis_fixed
    (P : PrincipalProjectionFieldSource field D)
    (projectiveStable : ∀ e : E, ∀ f : G → K, f ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace)
    (gggr_fixed : ∀ e : E, ∀ j : Fin n,
      functionTwistLinearEquiv (K := K) (field e).unop (D.gggr j) =
        D.gggr j) :
    ∀ e : E, ∀ j : CorollaryIndex.{u} n,
      projectiveFieldRepresentation field projectiveSpace
          projectiveStable e (corollaryGGGRBasis D j) =
        corollaryGGGRBasis D j := by
  intro e j
  rw [corollaryGGGRBasis, Basis.reindex_apply]
  exact P.gggrProjectiveBasis_fixed projectiveStable gggr_fixed e j.down

/-- Direct actual-carrier handoff from Proposition 4.9 and Lemma 4.7 to
Corollary 4.10.

`D.gggrProjectiveBasis` is kernel-constructed from the Proposition 4.9
source data.  `gggr_fixed` is the literal function-valued match to Lemma
4.7.  Projection naturality derives the `gggrBasis_fixed` argument required
by Corollary 4.10, after which that theorem derives Brauer fixedness from the
projective--Brauer formula.  Neither a basis nor any projected/basis/Brauer
fixedness statement is a premise. -/
theorem corollary_4_13_of_proposition_4_12_and_lemma_4_11
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (brauerStable : ∀ e : E, ∀ phi : IBr iota,
      inPrincipalBlock phi →
        inPrincipalBlock
          (IrreducibleBrauerCharacter.twist iota phi (field e).unop))
    (projectiveStable : ∀ e : E, ∀ f : G → K, f ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop f ∈ projectiveSpace)
    (B : ProjectiveBrauerFormulaSource field iota inPrincipalBlock
      brauerStable projectiveSpace projectiveStable)
    (P : PrincipalProjectionFieldSource field D)
    (gggr_fixed : ∀ e : E, ∀ j : Fin n,
      functionTwistLinearEquiv (K := K) (field e).unop (D.gggr j) =
        D.gggr j) :
    let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
    ∀ e : E, ∀ phi : PrincipalBrauerCarrier iota inPrincipalBlock,
      e • phi = phi := by
  exact ProjectiveBrauerFormulaSource.corollary_4_13_brauer_fixed_source_instantiated
    (p := p) (k := k) (K := K) (G := G) (E := E)
    (field := field) (iota := iota)
    (inPrincipalBlock := inPrincipalBlock)
    (brauerStable := brauerStable)
    (projectiveSpace := projectiveSpace)
    (projectiveStable := projectiveStable)
    (I := CorollaryIndex.{u} n) B (corollaryGGGRBasis D)
    (P.corollaryGGGRBasis_fixed projectiveStable gggr_fixed)

end PrincipalProjectionFieldSource

end ModularRep.PaperProofs.TypeBGGGRRankProposition412Corollary413Bridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
