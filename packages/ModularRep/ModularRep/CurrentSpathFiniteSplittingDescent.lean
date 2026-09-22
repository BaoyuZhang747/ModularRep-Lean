import ModularRep.CurrentSpathDescent
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# Central descent with explicit character correspondences

This form of manuscript Corollary 2.5 works with the ordinary coefficient
fields of the application. It does not assert that the fraction field of a
discrete valuation ring is algebraically closed. The character and weight
correspondences use one central quotient map and matched coefficient fields.
Lean transports the bijection of an established full family through those
correspondences. The passage of the extension and block conditions for each
of its pairs uses Spath (2013), Proposition 4.6, combined with Spath (2017),
Theorem 4.4, as an explicit external source.

The external source is uniform over the full family and its actual pairs.
It cannot choose a different target matching. Its coefficient hypothesis
concerns the finite extension groups in the given family witness.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.CurrentSpathFiniteSplittingDescent

open ModularRep CharacterWeight CurrentSpathDescent
open ModularRep.PaperProofs
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldFLZBAWGoodFamily CurrentCyclicOuterBAW
open TypeBFullBlockCondition

universe u

/-- Inflation of characters and lifting of weights through the specified
central quotient, on one block. These are correspondences of characters,
not an assumed matching between Brauer characters and weights. -/
structure BlockTransport {p : ℕ}
    (up down : Definition35Family.{u} p)
    (matchCover : EllPrimeCoverCentralExtensionFamilyMatch up down)
    (upBlock : up.Block) (downBlock : down.Block) where
  quotient : up.H →* down.H
  surjective : Function.Surjective quotient
  quotient_commutes : matchCover.targetQuotient.comp quotient = matchCover.cover.quotient
  coefficients : Coefficients up down
  /-- The acting group is exactly the full block stabiliser. This excludes
  arbitrary nonfaithful presentations of the same character action. -/
  downAutomorphisms : Definition35AutomorphismStabilizerAdapter (down.problem downBlock)
  brauer : Definition35Brauer (down.problem downBlock) ≃
    Definition35Brauer (up.problem upBlock)
  brauer_values : ∀ psi (x : PrimeRegularElement (G := up.H) p),
    coefficients.ordinary ((brauer psi).1.1 x) =
      psi.1.1 (PrimeRegularElement.map quotient x)
  weight : Definition35Weight (down.problem downBlock) ≃
    Definition35Weight (up.problem upBlock)
  downRaw : ∀ _w : Definition35Weight (down.problem downBlock),
    CharacterWeight p down.K down.H
  upRaw : ∀ _w : Definition35Weight (down.problem downBlock),
    CharacterWeight p up.K up.H
  downRaw_class : ∀ w,
    (Quotient.mk'' (Quotient.mk'' (downRaw w) : CharacterWeight.IsoClass) :
      CharacterWeight.ConjugacyClass) = w.1
  upRaw_class : ∀ w,
    (Quotient.mk'' (Quotient.mk'' (upRaw w) : CharacterWeight.IsoClass) :
      CharacterWeight.ConjugacyClass) = (weight w).1
  radical_image : ∀ w, (upRaw w).subgroup.map quotient = (downRaw w).subgroup
  normalizerMap : ∀ w,
    Subgroup.normalizer ((upRaw w).subgroup : Set up.H) →*
      Subgroup.normalizer ((downRaw w).subgroup : Set down.H)
  normalizer_values : ∀ w x, (normalizerMap w x).1 = quotient x.1
  normalizer_surjective : ∀ w, Function.Surjective (normalizerMap w)
  ordinary_values : ∀ w x,
    coefficients.ordinary ((upRaw w).localCharacter (QuotientGroup.mk x)) =
      (downRaw w).localCharacter (QuotientGroup.mk (normalizerMap w x))
  automorphisms : (down.problem downBlock).Gamma →* (up.problem upBlock).Gamma
  automorphisms_quotient : ∀ a x,
    quotient ((up.problem upBlock).gamma (automorphisms a) x) =
      (down.problem downBlock).gamma a (quotient x)
  brauer_equivariant :
    letI := definition35BrauerAction (up.problem upBlock)
    letI := definition35BrauerAction (down.problem downBlock)
    ∀ a psi, brauer (a • psi) = automorphisms a • brauer psi
  weight_equivariant :
    letI := definition35WeightAction (up.problem upBlock)
    letI := definition35WeightAction (down.problem downBlock)
    ∀ a w, weight (a • w) = automorphisms a • weight w

variable {p : ℕ} {up down : Definition35Family.{u} p}
  {matchCover : EllPrimeCoverCentralExtensionFamilyMatch up down}
  {upBlock : up.Block} {downBlock : down.Block}

/-- The transported map is fixed by the original full-family bijection. -/
def BlockTransport.bijection
    (T : BlockTransport up down matchCover upBlock downBlock)
    (W : FamilyWitness up matchCover.cover) :
    Definition35Brauer (down.problem downBlock) ≃
      Definition35Weight (down.problem downBlock) :=
  (T.brauer.trans (W.blocks upBlock).relative.omega).trans T.weight.symm

theorem BlockTransport.bijection_equivariant
    (T : BlockTransport up down matchCover upBlock downBlock)
    (W : FamilyWitness up matchCover.cover) :
    Definition35Equivariant (down.problem downBlock) (T.bijection W) := by
  let := definition35BrauerAction (up.problem upBlock)
  let := definition35BrauerAction (down.problem downBlock)
  let := definition35WeightAction (up.problem upBlock)
  let := definition35WeightAction (down.problem downBlock)
  intro a psi
  apply T.weight.injective
  change T.weight (T.weight.symm ((W.blocks upBlock).relative.omega
      (T.brauer (a • psi)))) =
    T.weight (a • T.weight.symm ((W.blocks upBlock).relative.omega (T.brauer psi)))
  rw [Equiv.apply_symm_apply, T.brauer_equivariant,
    (W.blocks upBlock).relative.equivariant, T.weight_equivariant,
    Equiv.apply_symm_apply]

/-- Both ordinary fields contain the roots used by the finite extension
groups in this witness. Existence is an explicit coefficient assumption,
not inferred from splitting the original covering group alone. -/
def CoefficientAdequacy
    (down : Definition35Family.{u} p)
    {cover : EllPrimeCoverSource p up.H}
    (W : FamilyWitness up cover) : Prop :=
  ∀ (b : up.Block) (psi : Definition35Brauer (up.problem b)),
    HasEnoughRootsOfUnity up.K
      (Nat.card ((W.blocks b).relative.matched psi).ambient.A) ∧
    HasEnoughRootsOfUnity down.K
      (Nat.card ((W.blocks b).relative.matched psi).ambient.A)

/-- External central descent for all families satisfying the stated cover, centre, character,
block transport and coefficient hypotheses, including roots for the actual ambient extension groups.
The conclusion uses the specified transported matching on each pair of an existing full family.
No target block witness is an input. -/
structure Source : Prop where
  matched : ∀ {p : ℕ} (up down : Definition35Family.{u} p)
      (matchCover : EllPrimeCoverCentralExtensionFamilyMatch up down)
      (_centerless : Subgroup.center down.H = ⊥)
      (_upPhysical : CurrentSpathDescent.PhysicalFamilySource up)
      (_downPhysical : CurrentSpathDescent.PhysicalFamilySource down)
      (_upField : SpathCoefficientField p up.k up.ellPrime)
      (_downField : SpathCoefficientField p down.k down.ellPrime)
      (upBlock : up.Block) (downBlock : down.Block)
      (T : BlockTransport up down matchCover upBlock downBlock)
      (W : FamilyWitness up matchCover.cover),
    CoefficientAdequacy down W →
    ∀ psi : Definition35Brauer (down.problem downBlock),
      Nonempty (CoherentMatchedCondition (down.problem downBlock) psi
        (T.bijection W psi))

/-- Corollary 2.5 on a specified block, using finite splitting and the
bijection already established on the covering group. -/
theorem current_corollary_2_5_block
    (source : Source.{u})
    (centerless : Subgroup.center down.H = ⊥)
    (upPhysical : CurrentSpathDescent.PhysicalFamilySource up)
    (downPhysical : CurrentSpathDescent.PhysicalFamilySource down)
    (upField : SpathCoefficientField p up.k up.ellPrime)
    (downField : SpathCoefficientField p down.k down.ellPrime)
    (T : BlockTransport up down matchCover upBlock downBlock)
    (W : FamilyWitness up matchCover.cover)
    (adequate : CoefficientAdequacy down W) :
    Nonempty (CoherentBlockBijection down downBlock) := by
  refine ⟨{ omega := T.bijection W
            equivariant := T.bijection_equivariant W
            matched := ?_ }⟩
  intro psi
  exact Classical.choice (source.matched up down matchCover centerless
    upPhysical downPhysical upField downField upBlock downBlock T W adequate psi)

end ModularRep.CurrentSpathFiniteSplittingDescent

/-
This file is part of the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The formalisation checks selected arguments under explicit external assumptions.
-/
