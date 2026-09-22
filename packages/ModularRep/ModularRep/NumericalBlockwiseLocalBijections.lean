import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

/-!
# Numerical blockwise local bijections

This source-neutral module turns blockwise finite-cardinality equalities into
a selected block-preserving equivalence, its radical-label partition, and the
induced equivalences on block/radical fibres.  The choice is noncanonical.

The final theorem is deliberately map-independent: an arbitrary equivalence
between a subsingleton source block fibre and its target block fibre must send
the distinguished source point to the distinguished target point.  No
character-theoretic correspondence or completeness statement is assumed.
-/

noncomputable section

namespace ModularRep.NumericalBlockwiseLocalBijections

universe uB uX uY uRad uD

variable {B : Type uB} {X : Type uX} {Y : Type uY} {Rad : Type uRad} {D : Type uD}

def BlockwiseCardinality [Fintype X] [Fintype Y] [DecidableEq B]
    (sourceBlock : X → B) (targetBlock : Y → B) : Prop :=
  ∀ b : B,
    Fintype.card {x : X // sourceBlock x = b} =
      Fintype.card {y : Y // targetBlock y = b}

noncomputable def blockFibreEquiv [Fintype X] [Fintype Y]
    [DecidableEq B] (sourceBlock : X → B) (targetBlock : Y → B)
    (hcard : BlockwiseCardinality sourceBlock targetBlock) (b : B) :
    {x : X // sourceBlock x = b} ≃ {y : Y // targetBlock y = b} :=
  Fintype.equivOfCardEq (hcard b)

noncomputable def globalEquiv [Fintype X] [Fintype Y]
    [DecidableEq B] (sourceBlock : X → B) (targetBlock : Y → B)
    (hcard : BlockwiseCardinality sourceBlock targetBlock) : X ≃ Y :=
  (Equiv.sigmaFiberEquiv sourceBlock).symm |>.trans
    (Equiv.sigmaCongrRight (blockFibreEquiv sourceBlock targetBlock hcard)) |>.trans
    (Equiv.sigmaFiberEquiv targetBlock)

theorem globalEquiv_block [Fintype X] [Fintype Y] [DecidableEq B]
    (sourceBlock : X → B) (targetBlock : Y → B)
    (hcard : BlockwiseCardinality sourceBlock targetBlock) (x : X) :
    targetBlock (globalEquiv sourceBlock targetBlock hcard x) = sourceBlock x :=
  (blockFibreEquiv sourceBlock targetBlock hcard (sourceBlock x)
    ⟨x, rfl⟩).2

noncomputable def part [Fintype X] [Fintype Y] [DecidableEq B]
    (sourceBlock : X → B) (targetBlock : Y → B) (targetRadical : Y → Rad)
    (hcard : BlockwiseCardinality sourceBlock targetBlock) (x : X) : Rad :=
  targetRadical (globalEquiv sourceBlock targetBlock hcard x)

noncomputable def partitionEquiv [Fintype X] [Fintype Y] [DecidableEq B]
    (sourceBlock : X → B) (targetBlock : Y → B) (targetRadical : Y → Rad)
    (hcard : BlockwiseCardinality sourceBlock targetBlock) :
    X ≃ Σ r : Rad, {x : X // part sourceBlock targetBlock targetRadical hcard x = r} :=
  (Equiv.sigmaFiberEquiv (part sourceBlock targetBlock targetRadical hcard)).symm

noncomputable def localFibreEquiv [Fintype X] [Fintype Y] [DecidableEq B]
    (sourceBlock : X → B) (targetBlock : Y → B) (targetRadical : Y → Rad)
    (hcard : BlockwiseCardinality sourceBlock targetBlock)
    (b : B) (r : Rad) :
    {x : X // sourceBlock x = b ∧
      part sourceBlock targetBlock targetRadical hcard x = r} ≃
    {y : Y // targetBlock y = b ∧ targetRadical y = r} := by
  let e := globalEquiv sourceBlock targetBlock hcard
  refine
    { toFun := fun x ↦ ⟨e x, ?_⟩
      invFun := fun y ↦ ⟨e.symm y, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ⟨by
      rw [globalEquiv_block sourceBlock targetBlock hcard x.1, x.2.1],
      x.2.2⟩
  · constructor
    · calc
        sourceBlock (e.symm y) = targetBlock (e (e.symm y)) :=
          (globalEquiv_block sourceBlock targetBlock hcard (e.symm y)).symm
        _ = targetBlock y := by rw [e.apply_symm_apply]
        _ = b := y.2.1
    · change targetRadical (e (e.symm y)) = r
      rw [e.apply_symm_apply]
      exact y.2.2
  · intro x
    apply Subtype.ext
    exact e.symm_apply_apply x
  · intro y
    apply Subtype.ext
    exact e.apply_symm_apply y

theorem blockFibreEquiv_apply_eq_atOne_of_sourceSubsingleton
    (sourceBlock : X → B) (targetBlock : Y → B)
    (red : D → X) (atOne : D → Y)
    (d : D) (b : B)
    (hred : sourceBlock (red d) = b)
    (hatOne : targetBlock (atOne d) = b)
    (hsource : Subsingleton {x : X // sourceBlock x = b})
    (e : {x : X // sourceBlock x = b} ≃
      {y : Y // targetBlock y = b}) :
    (e ⟨red d, hred⟩).1 = atOne d := by
  let x : {x : X // sourceBlock x = b} := ⟨red d, hred⟩
  let y : {y : Y // targetBlock y = b} := ⟨atOne d, hatOne⟩
  have hpre : e.symm y = x := @Subsingleton.elim _ hsource _ _
  have hxy : e x = y := by
    rw [← hpre, e.apply_symm_apply]
  exact congrArg Subtype.val hxy

end ModularRep.NumericalBlockwiseLocalBijections


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
