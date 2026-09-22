import ModularRep.PaperProofs.TypeCIntermediateNormalizerComparison
import ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

/-!
# Actual Frattini factorization from the same weight orbit

The elementary group lemma derives X join N_A(Q) = top from the statement
that each A-conjugate of Q is X-conjugate. The weight consumer obtains
that statement from equality in the TWO actual weight quotients: it first
extracts an inner correction of the WHOLE raw pair, then maps the subgroup
component through the fixed base equivalence and inclusion.

The concrete relative-target consumer uses its already constructed quotient
raw weight, its actual ambient group, and the existing quotient matching's
equivariance. Ambient Brauer fixation is derived from the stored natural
automorphism-stabilizer equivalence. No Frattini, independent subgroup
equality, root equality, or final-target premise is introduced.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCActualFrattiniFromWeightOrbit

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete
open OddTwoSelectedWeightAutomorphismCoordinates
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre

universe u

section Groups

variable {A : Type u} [Group A]

/-- Exact composition of the actual conjugation homomorphisms. -/
theorem conjugation_mul (x y : A) :
    (MulAut.conj (x * y)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
  apply MonoidHom.ext
  intro z
  change (x * y) * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹
  simp only [mul_inv_rev, mul_assoc]

/-- An actual equality of conjugate subgroups gives a normalizing correction. -/
theorem correction_mem_normalizer (Q : Subgroup A) (a x : A)
    (hconj : Q.map (MulAut.conj a).toMonoidHom =
      Q.map (MulAut.conj x).toMonoidHom) :
    x⁻¹ * a ∈ Subgroup.normalizer (Q : Set A) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Q.map (MulAut.conj (x⁻¹ * a)).toMonoidHom = Q
  rw [conjugation_mul, ← Subgroup.map_map, hconj, Subgroup.map_map]
  have hcancel : (MulAut.conj x⁻¹).toMonoidHom.comp
      (MulAut.conj x).toMonoidHom = MonoidHom.id A := by
    apply MonoidHom.ext
    intro z
    change x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ = z
    simp [mul_assoc]
  rw [hcancel, Subgroup.map_id]

/-- The Frattini factorization follows from the actual subgroup orbit.
Normality of X is not needed for this elementary implication. -/
theorem sup_normalizer_eq_top_of_conjugate_orbit (X Q : Subgroup A)
    (orbit : ∀ a : A, ∃ x : X,
      Q.map (MulAut.conj a).toMonoidHom =
        Q.map (MulAut.conj (x : A)).toMonoidHom) :
    X ⊔ Subgroup.normalizer (Q : Set A) = ⊤ := by
  apply top_unique
  intro a _ha
  obtain ⟨x, hx⟩ := orbit a
  have hn := correction_mem_normalizer Q a (x : A) hx
  have hprod := Subgroup.mul_mem_sup x.2 hn
  simpa only [mul_inv_cancel_left] using hprod

/-- The reverse calculation exposes the actual subgroup-orbit statement
from a normalizing product, with its exact inner element. -/
theorem conjugate_eq_of_normalizing_product (Q : Subgroup A) (x a : A)
    (hn : x * a ∈ Subgroup.normalizer (Q : Set A)) :
    Q.map (MulAut.conj a).toMonoidHom =
      Q.map (MulAut.conj x⁻¹).toMonoidHom := by
  have hQ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  change Q.map (MulAut.conj (x * a)).toMonoidHom = Q at hQ
  have heq := congrArg
    (fun R : Subgroup A => R.map (MulAut.conj x⁻¹).toMonoidHom) hQ
  rw [Subgroup.map_map] at heq
  have hcancel : (MulAut.conj x⁻¹).toMonoidHom.comp
      (MulAut.conj (x * a)).toMonoidHom = (MulAut.conj a).toMonoidHom := by
    rw [← conjugation_mul]
    simp only [inv_mul_cancel_left]
  rw [hcancel] at heq
  exact heq

/-- The internal local subgroup and its ambient intersection have the
same elements, retaining both membership proofs explicitly. -/
def intersectionEquiv (J N : Subgroup A) :
    ↥(N.comap J.subtype) ≃* ↥(J ⊓ N) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def intersectionToGlobal (J N : Subgroup A) : ↥(J ⊓ N) →* J where
  toFun x := ⟨x.1, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def intersectionToLocal (J N : Subgroup A) : ↥(J ⊓ N) →* N where
  toFun x := ⟨x.1, x.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def internalToLocal (J N : Subgroup A) : ↥(N.comap J.subtype) →* N where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem intersectionEquiv_coe (J N : Subgroup A) (x : N.comap J.subtype) :
    (intersectionEquiv J N x : A) = x.1.1 := rfl

theorem intersectionEquiv_global_square (J N : Subgroup A) :
    (intersectionToGlobal J N).comp (intersectionEquiv J N).toMonoidHom =
      (N.comap J.subtype).subtype := by
  apply MonoidHom.ext
  intro x
  rfl

theorem intersectionEquiv_local_square (J N : Subgroup A) :
    (intersectionToLocal J N).comp (intersectionEquiv J N).toMonoidHom =
      internalToLocal J N := by
  apply MonoidHom.ext
  intro x
  rfl

end Groups

section ActualWeight

variable {p : ℕ} {K H A : Type u}
variable [Field K] [CharZero K] [Group H] [Fintype H] [Group A]
variable (X : Subgroup A) (e : H ≃* X)
variable (rho : A →* MulAut H)

/-- The specified base equivalence followed by the literal subgroup inclusion. -/
def baseEmbedding : H →* A := X.subtype.comp e.toMonoidHom

/-- The actual image of the subgroup of this OWN raw character weight. -/
def embeddedRadical (W : CharacterWeight p K H) : Subgroup A :=
  W.subgroup.map (baseEmbedding X e)

theorem embeddedRadical_le_base (W : CharacterWeight p K H) :
    embeddedRadical X e W ≤ X := by
  rintro y ⟨x, _hx, rfl⟩
  exact (e x).2

variable (conjugation : ∀ (a : A) (h : H),
  baseEmbedding X e (rho a h) =
    a * baseEmbedding X e h * a⁻¹)

include conjugation in
/-- The whole-pair correction uses this exact square of group maps. -/
theorem correctedEmbedding_square (g : H) (a : A) :
    (baseEmbedding X e).comp (coordinateAutomorphism g (rho a)).toMonoidHom =
      (MulAut.conj (baseEmbedding X e g * a)).toMonoidHom.comp
        (baseEmbedding X e) := by
  apply MonoidHom.ext
  intro h
  change baseEmbedding X e (g * rho a h * g⁻¹) =
    (baseEmbedding X e g * a) * baseEmbedding X e h *
      (baseEmbedding X e g * a)⁻¹
  rw [map_mul, map_mul, map_inv, conjugation]
  simp only [mul_inv_rev, mul_assoc]

include conjugation in
/-- Extract a correction of the ENTIRE own pair from the actual class
equality; its embedded element consequently normalizes the actual radical. -/
theorem exists_own_pair_normalizing_correction (W : CharacterWeight p K H)
    (a : A)
    (fixed : rightTwistConjugacyClass (rho a)⁻¹ (weightClass W) = weightClass W) :
    ∃ g : H,
      W.rightTwist (coordinateAutomorphism g (rho a))⁻¹ = W ∧
      baseEmbedding X e g * a ∈
        Subgroup.normalizer (embeddedRadical X e W : Set A) := by
  obtain ⟨g, hpair⟩ := exists_coordinate_of_class_eq W W (rho a) fixed.symm
  refine ⟨g, hpair, ?_⟩
  have hsub := coordinate_subgroup W W g (rho a) hpair
  have heq := congrArg (fun R : Subgroup H => R.map (baseEmbedding X e)) hsub
  rw [Subgroup.map_map, correctedEmbedding_square X e rho conjugation] at heq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (W.subgroup.map (baseEmbedding X e)).map
    (MulAut.conj (baseEmbedding X e g * a)).toMonoidHom =
      W.subgroup.map (baseEmbedding X e)
  rw [Subgroup.map_map]
  exact heq

include conjugation in
/-- Every ambient conjugate is conjugate by an actual element of X,
derived from class fixation of the same raw weight. -/
theorem embeddedRadical_conjugate_orbit (W : CharacterWeight p K H)
    (fixed : ∀ a : A,
      rightTwistConjugacyClass (rho a)⁻¹ (weightClass W) = weightClass W) :
    ∀ a : A, ∃ x : X,
      (embeddedRadical X e W).map (MulAut.conj a).toMonoidHom =
        (embeddedRadical X e W).map (MulAut.conj (x : A)).toMonoidHom := by
  intro a
  obtain ⟨g, _hpair, hn⟩ :=
    exists_own_pair_normalizing_correction X e rho conjugation W a (fixed a)
  refine ⟨(e g)⁻¹, ?_⟩
  exact conjugate_eq_of_normalizing_product (embeddedRadical X e W)
    (baseEmbedding X e g) a hn

include conjugation in
theorem frattini_of_weightClass_fixed (W : CharacterWeight p K H)
    (fixed : ∀ a : A,
      rightTwistConjugacyClass (rho a)⁻¹ (weightClass W) = weightClass W) :
    X ⊔ Subgroup.normalizer (embeddedRadical X e W : Set A) = ⊤ :=
  sup_normalizer_eq_top_of_conjugate_orbit X (embeddedRadical X e W)
    (embeddedRadical_conjugate_orbit X e rho conjugation W fixed)

include conjugation in
/-- Every actual intermediate J is covered after the Frattini premise
has been derived from the same weight, rather than supplied separately. -/
theorem intermediate_eq_of_weightClass_fixed [X.Normal]
    (W : CharacterWeight p K H)
    (fixed : ∀ a : A,
      rightTwistConjugacyClass (rho a)⁻¹ (weightClass W) = weightClass W)
    (J : Subgroup A) (hXJ : X ≤ J) :
    J = X ⊔ (J ⊓ Subgroup.normalizer (embeddedRadical X e W : Set A)) :=
  TypeCIntermediateNormalizerComparison.intermediate_eq_join_inf X
    (Subgroup.normalizer (embeddedRadical X e W : Set A)) J hXJ
    (frattini_of_weightClass_fixed X e rho conjugation W fixed)

end ActualWeight

section CompleteRelativeTarget

open TypeBFullBlockCondition

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable (B : BlockWitness family cover block)
variable (psi : Definition35Brauer (family.problem block))

/-- Its ambient group fixes its OWN descended Brauer character, by the
existing actual automorphism-stabilizer coordinate equation. -/
theorem matchedBrauer_fixed (a : (B.relative.matched psi).ambient.A) :
    inverseOpHom (B.relative.matched psi).ambient.conjugation a •
        (B.relative.matched psi).quotient.brauer =
      (B.relative.matched psi).quotient.brauer := by
  let ambient := (B.relative.matched psi).ambient
  have hf := (ambient.automorphismQuotientEquiv
    (QuotientGroup.mk' (Subgroup.center ambient.A) a)).2
  change ((ambient.automorphismQuotientEquiv
    (QuotientGroup.mk' (Subgroup.center ambient.A) a)) :
      (MulAut (QuotientCarrier B.relative))ᵐᵒᵖ) •
      (B.relative.matched psi).quotient.brauer =
        (B.relative.matched psi).quotient.brauer at hf
  rw [ambient.automorphismQuotientEquiv_natural] at hf
  exact hf

/-- Moving to the already stored reference root leaves the actual class
function unchanged. No equality of independent roots is introduced. -/
theorem fixedDescendedBrauer_fixed (a : (B.relative.matched psi).ambient.A) :
    inverseOpHom (B.relative.matched psi).ambient.conjugation a •
        fixedDescendedBrauer B.relative B.roots psi =
      fixedDescendedBrauer B.relative B.roots psi := by
  apply Subtype.ext
  rw [IrreducibleBrauerCharacter.op_smul_val, fixedDescendedBrauer_val]
  have hf := congrArg Subtype.val (matchedBrauer_fixed B psi a)
  rw [IrreducibleBrauerCharacter.op_smul_val] at hf
  exact hf

/-- The EXISTING complete matching's equivariance supplies fixation of
the same quotient raw weight's ambient class. -/
theorem quotientWeightClass_fixed (a : (B.relative.matched psi).ambient.A) :
    rightTwistConjugacyClass ((B.relative.matched psi).ambient.conjugation a)⁻¹
      (quotientWeightClass B.relative psi) =
        quotientWeightClass B.relative psi := by
  have hf := B.quotient_equivariant
    (inverseOpHom (B.relative.matched psi).ambient.conjugation a) psi psi
    (fixedDescendedBrauer_fixed B psi a).symm
  change quotientWeightClass B.relative psi =
    rightTwistConjugacyClass ((B.relative.matched psi).ambient.conjugation a⁻¹)
      (quotientWeightClass B.relative psi) at hf
  rw [map_inv] at hf
  exact hf.symm

/-- The actual target's ambient group factors through the normalizer of
its actual selected quotient radical. No factorization is a new field. -/
theorem matched_frattini :
    (B.relative.matched psi).ambient.base ⊔
      AmbientLocalGroup (family.problem block) B.relative.reference psi
        (B.relative.omega psi) (B.relative.matched psi).quotient
          (B.relative.matched psi).ambient = ⊤ := by
  letI : Fintype (QuotientCarrier B.relative) := Fintype.ofFinite _
  let ambient := (B.relative.matched psi).ambient
  exact frattini_of_weightClass_fixed ambient.base ambient.baseEquiv
    ambient.conjugation ambient.conjugation_on_base
    (quotientRawWeight B.relative psi) (quotientWeightClass_fixed B psi)

/-- All J containing the SAME base are now covered by the direct-H
presentation, with H = J intersect the SAME ambient normalizer. -/
theorem matched_intermediate_eq (J : Subgroup (B.relative.matched psi).ambient.A)
    (hJ : (B.relative.matched psi).ambient.base ≤ J) :
    J = (B.relative.matched psi).ambient.base ⊔
      (J ⊓ AmbientLocalGroup (family.problem block) B.relative.reference psi
        (B.relative.omega psi) (B.relative.matched psi).quotient
          (B.relative.matched psi).ambient) :=
  TypeCIntermediateNormalizerComparison.intermediate_eq_join_inf
    (B.relative.matched psi).ambient.base
    (AmbientLocalGroup (family.problem block) B.relative.reference psi
      (B.relative.omega psi) (B.relative.matched psi).quotient
        (B.relative.matched psi).ambient) J hJ (matched_frattini B psi)

/-- The relative target's NAMED local inclusion is preserved by this
same intersection equivalence at every actual J. -/
theorem matched_intermediate_local_square
    (J : Subgroup (B.relative.matched psi).ambient.A) :
    (intersectionToLocal J
      (AmbientLocalGroup (family.problem block) B.relative.reference psi
        (B.relative.omega psi) (B.relative.matched psi).quotient
          (B.relative.matched psi).ambient)).comp
      (intersectionEquiv J
        (AmbientLocalGroup (family.problem block) B.relative.reference psi
          (B.relative.omega psi) (B.relative.matched psi).quotient
            (B.relative.matched psi).ambient)).toMonoidHom =
      intermediateLocalToAmbientLocal (w := B.relative.omega psi)
        (B.relative.matched psi).ambient J := by
  apply MonoidHom.ext
  intro x
  rfl

/-- The global restriction subgroup is the original J, with its original
inclusion rather than a newly chosen isomorphic intermediate group. -/
theorem matched_intermediate_global_square
    (J : Subgroup (B.relative.matched psi).ambient.A) :
    (intersectionToGlobal J
      (AmbientLocalGroup (family.problem block) B.relative.reference psi
        (B.relative.omega psi) (B.relative.matched psi).quotient
          (B.relative.matched psi).ambient)).comp
      (intersectionEquiv J
        (AmbientLocalGroup (family.problem block) B.relative.reference psi
          (B.relative.omega psi) (B.relative.matched psi).quotient
            (B.relative.matched psi).ambient)).toMonoidHom =
      (IntermediateLocalNormalizer (w := B.relative.omega psi)
        (B.relative.matched psi).ambient J).subtype := by
  apply MonoidHom.ext
  intro x
  rfl

end CompleteRelativeTarget

end ModularRep.PaperProofs.TypeCActualFrattiniFromWeightOrbit


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
