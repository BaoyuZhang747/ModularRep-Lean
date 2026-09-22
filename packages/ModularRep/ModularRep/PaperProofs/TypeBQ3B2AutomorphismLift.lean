import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionAutomorphisms
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv

/-!
Every automorphism of the actual matrix G3 lifts to the retained triple
cover X. The already proved lifting theorem is applied to the universal
six-cover FullCover. Its intrinsic central two-subgroup is characteristic,
so the lifted automorphism descends to X. Universality is never asserted
for X, and no new automorphism-lifting source is introduced.

The existing literal Brauer inflation square then transports full
automorphism fixedness to G3 for any character, without a principal-block
assumption or any correspondence of weights.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3B2AutomorphismLift

open ModularRep
open TypeBQ3TripleCoverCarrier TypeBQ3TripleCoverAutomorphisms
open TypeBQ3PrincipalCriterionAutomorphisms
open SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

/-- Lift on the full universal cover, then descend through its characteristic C2. -/
theorem exists_lift (beta : MulAut G3) :
    ∃ alpha : MulAut X, ∀ x : X,
      q matrixSource freeSource (alpha x) = beta (q matrixSource freeSource x) := by
  obtain ⟨gamma, square⟩ := exists_aut_lift fullProjection
    (fullProjection_universal matrixSource freeSource) beta
  have invariant : centralTwoSubgroup.map gamma.toMonoidHom = centralTwoSubgroup :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance gamma
  let alpha : MulAut X := QuotientGroup.congr centralTwoSubgroup
    centralTwoSubgroup gamma invariant
  refine ⟨alpha, ?_⟩
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  change fullProjection (gamma y) = beta (fullProjection y)
  exact square y

/-- The canonical descent map covers every actual downstairs automorphism. -/
theorem descendHom_surjective :
    Function.Surjective (descendHom matrixSource freeSource) := by
  intro beta
  obtain ⟨alpha, square⟩ := exists_lift matrixSource freeSource beta
  refine ⟨alpha, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := q_surjective matrixSource freeSource y
  exact (descendAutomorphism_apply_q matrixSource freeSource alpha x).trans (square x)

theorem descendOppositeHom_surjective :
    Function.Surjective (descendOppositeHom matrixSource freeSource) := by
  intro beta
  obtain ⟨alpha, same⟩ := descendHom_surjective matrixSource freeSource beta.unop
  refine ⟨MulOpposite.op alpha, ?_⟩
  change MulOpposite.op (descendHom matrixSource freeSource alpha) = beta
  exact congrArg MulOpposite.op same

variable [Finite X]
variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

/-- Full fixedness descends along the same root-compatible character inflation. -/
theorem fixed_downstairs
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (phiX : IBr rootX)
    (phiDown : IBr (rootDown matrixSource freeSource rootX))
    (values : PrimeRegularClassFunction.pullback (q matrixSource freeSource) phiDown.val =
      phiX.val)
    (fixedUp : ∀ alpha : (MulAut X)ᵐᵒᵖ, alpha • phiX = phiX)
    (beta : (MulAut G3)ᵐᵒᵖ) : beta • phiDown = phiDown := by
  obtain ⟨alpha, rfl⟩ := descendOppositeHom_surjective matrixSource freeSource beta
  exact (fixed_iff matrixSource freeSource rootX phiX phiDown values alpha).mp (fixedUp alpha)

end ModularRep.PaperProofs.TypeBQ3B2AutomorphismLift


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
