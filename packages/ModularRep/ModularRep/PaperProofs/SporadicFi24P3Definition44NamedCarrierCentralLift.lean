import ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The literal central character condition when X is centreless

An ordinary irreducible character of the trivial centre is identically one,
over any characteristic-zero field. Inflating an actual normalizer-quotient
character therefore lies over every such central character. This is the
centreless instance of Spath Definition 4.1(ii)(1).
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralLift

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal

universe u

theorem ordinaryIrr_apply_eq_one_of_subsingleton
    {K G : Type u} [Field K] [CharZero K] [Group G] [Subsingleton G]
    (chi : OrdinaryIrreducibleCharacter.Irr K G) (g : G) : chi g = 1 := by
  obtain ⟨R⟩ := chi.2
  let e : Subrepresentation R.representation ≃o Submodule K (Fin R.dimension → K) := {
    toFun := Subrepresentation.toSubmodule
    invFun := fun S => {
      toSubmodule := S
      apply_mem_toSubmodule := by
        intro a v hv
        simpa only [Subsingleton.elim a 1, map_one, Module.End.one_apply] using hv }
    left_inv := fun W => Subrepresentation.ext rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  have hsimple : IsSimpleModule K (Fin R.dimension → K) :=
    (isSimpleModule_iff K (Fin R.dimension → K)).mpr
      ((OrderIso.isSimpleOrder_iff e).mp R.irreducible)
  have hdim : Module.finrank K (Fin R.dimension → K) = 1 :=
    isSimpleModule_iff_finrank_eq_one.mp hsimple
  calc
    chi g = R.representation.character g := (congrFun R.character_eq g).symm
    _ = R.representation.character 1 := congrArg _ (Subsingleton.elim g 1)
    _ = (Module.finrank K (Fin R.dimension → K) : K) := Representation.char_one _
    _ = 1 := by rw [hdim, Nat.cast_one]

theorem exists_ordinary_lift_over_center
    {K X : Type u} [Field K] [CharZero K] [Group X] [Fintype X]
    (hcenter : Subgroup.center X = ⊥) (Q : Subgroup X)
    (theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)) :
    let N := Subgroup.normalizer (Q : Set X)
    ∃ thetaHat : OrdinaryIrreducibleCharacter.Irr K N,
      (∀ n : N, thetaHat n = theta (QuotientGroup.mk n)) ∧
      ∀ nu : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center X),
        ∀ z : Subgroup.center X,
          thetaHat ⟨z.1, Subgroup.center_le_normalizer (Q : Set X) z.2⟩ =
            thetaHat 1 * nu z := by
  let N := Subgroup.normalizer (Q : Set X)
  let R := Q.subgroupOf N
  let thetaHat := inflateOrdinaryCharacter R theta
  let : Subsingleton (Subgroup.center X) :=
    ⟨fun z w => Subtype.ext
      (((Subgroup.eq_bot_iff_forall _).mp hcenter z.1 z.2).trans
        ((Subgroup.eq_bot_iff_forall _).mp hcenter w.1 w.2).symm)⟩
  refine ⟨thetaHat, fun _ => rfl, ?_⟩
  intro nu z
  have hz : z.1 = 1 := (Subgroup.eq_bot_iff_forall _).mp hcenter z.1 z.2
  have hzN : (⟨z.1, Subgroup.center_le_normalizer (Q : Set X) z.2⟩ : N) = 1 :=
    Subtype.ext hz
  rw [hzN, ordinaryIrr_apply_eq_one_of_subsingleton nu z, mul_one]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralLift


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
