import ModularRep.PaperProofs.TypeBQ3TripleCoverAutomorphisms
import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

/-!
# The actual upstairs inertia as a subgroup of the downstairs ambient

The fixed projection from the canonical triple cover gives an injective
homomorphism on automorphism groups. Injectivity compares two maps from the
full central cover into this triple cover, using the universal property only
of the full cover and then the surjectivity of its quotient projection.

Literal Brauer inflation restricts this homomorphism to the opposite
character stabilizers. The resulting image contains the existing inner
base, with the exact projection square. The value equality used here is the
one supplied by the accepted principal Brauer deflation. There is no added
literature source or automorphism-surjectivity assumption. This is a support
deduction for the criterion consumer, with no standalone manuscript claim.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionAutomorphisms

open ModularRep
open TypeBQ3TripleCoverCarrier TypeBQ3TripleCoverAutomorphisms
open IrreducibleBrauerCharacterSurjectiveDescent
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

variable (source : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

/-- Descent along the fixed projection respects composition. -/
def descendHom : MulAut X →* MulAut G3 where
  toFun := descendAutomorphism source freeSource
  map_one' := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := q_surjective source freeSource y
    rw [descendAutomorphism_apply_q]
    rfl
  map_mul' alpha beta := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := q_surjective source freeSource y
    change descendAutomorphism source freeSource (alpha * beta) (q source freeSource x) =
      descendAutomorphism source freeSource alpha
        (descendAutomorphism source freeSource beta (q source freeSource x))
    rw [descendAutomorphism_apply_q, descendAutomorphism_apply_q,
      descendAutomorphism_apply_q]
    rfl

/-- An automorphism over the identity is detected by the actual full-cover
quotient projection. Universality is used on FullCover, not on X. -/
theorem automorphism_eq_one_of_square (alpha : MulAut X)
    (square : ∀ x : X, q source freeSource (alpha x) = q source freeSource x) :
    alpha = 1 := by
  let pi : FullCover →* X := QuotientGroup.mk' centralTwoSubgroup
  obtain ⟨lift, _, unique⟩ :=
    (fullProjection_universal source freeSource).2 X (q source freeSource)
      ⟨q_surjective source freeSource, q_kernel_le_center source freeSource⟩
  have hleft : (q source freeSource).comp (alpha.toMonoidHom.comp pi) =
      fullProjection := by
    apply MonoidHom.ext
    intro x
    exact (square (pi x)).trans (q_mk source freeSource x)
  have hright : (q source freeSource).comp pi = fullProjection := by
    apply MonoidHom.ext
    intro x
    exact q_mk source freeSource x
  have same : alpha.toMonoidHom.comp pi = pi :=
    (unique _ hleft).trans (unique _ hright).symm
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective centralTwoSubgroup x
  exact DFunLike.congr_fun same y

/-- The descended group automorphism determines the original one. -/
theorem descendHom_injective : Function.Injective (descendHom source freeSource) := by
  apply (MonoidHom.ker_eq_bot_iff (descendHom source freeSource)).mp
  apply le_antisymm ?_ bot_le
  intro alpha ha
  apply Subgroup.mem_bot.mpr
  apply automorphism_eq_one_of_square source freeSource alpha
  intro x
  change descendAutomorphism source freeSource alpha = 1 at ha
  calc
    q source freeSource (alpha x) =
        descendAutomorphism source freeSource alpha (q source freeSource x) :=
      (descendAutomorphism_apply_q source freeSource alpha x).symm
    _ = (1 : MulAut G3) (q source freeSource x) :=
      congrArg (fun beta : MulAut G3 => beta (q source freeSource x)) ha
    _ = q source freeSource x := rfl

/-- Descent takes literal inner automorphisms to those of the projected element. -/
theorem descendHom_conj (x : X) :
    descendHom source freeSource (MulAut.conj x) = MulAut.conj (q source freeSource x) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := q_surjective source freeSource y
  change descendAutomorphism source freeSource (MulAut.conj x) (q source freeSource z) = _
  rw [descendAutomorphism_apply_q]
  change q source freeSource (x * z * x⁻¹) =
    q source freeSource x * q source freeSource z * (q source freeSource x)⁻¹
  exact ((q source freeSource).map_mul' (x * z) x⁻¹).trans
    (congrArg₂ (fun a b : G3 => a * b)
      ((q source freeSource).map_mul' x z) ((q source freeSource).map_inv x))

/-- The existing Brauer action uses the opposite automorphism group. -/
def descendOppositeHom : (MulAut X)ᵐᵒᵖ →* (MulAut G3)ᵐᵒᵖ :=
  (descendHom source freeSource).op

theorem descendOppositeHom_injective :
    Function.Injective (descendOppositeHom source freeSource) := by
  intro alpha beta same
  apply MulOpposite.unop_injective
  apply descendHom_injective source freeSource
  exact congrArg MulOpposite.unop same

theorem descendOppositeHom_square (alpha : (MulAut X)ᵐᵒᵖ) (x : X) :
    q source freeSource (alpha.unop x) =
      (descendOppositeHom source freeSource alpha).unop (q source freeSource x) :=
  (descendAutomorphism_apply_q source freeSource alpha.unop x).symm

-- The actual consumer installs this instance using finite_X source.
variable [Finite X]
variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (rootX : PrimeRegularRootEmbedding 2 k K X)

/-- The same root convention used by the accepted principal deflation. -/
abbrev rootDown : PrimeRegularRootEmbedding 2 k K G3 :=
  TypeBQ3PrincipalBrauerInflation.downRoot
    (q source freeSource) (q_surjective source freeSource) rootX

variable (phiX : IBr rootX) (phiDown : IBr (rootDown source freeSource rootX))
  (values : PrimeRegularClassFunction.pullback (q source freeSource) phiDown.val = phiX.val)

include values in
/-- Character stabilizers correspond along the actual injective descent map.
The equality of functions is supplied by literal principal deflation. -/
theorem fixed_iff (alpha : (MulAut X)ᵐᵒᵖ) :
    alpha • phiX = phiX ↔
      descendOppositeHom source freeSource alpha • phiDown = phiDown := by
  have natural : PrimeRegularClassFunction.pullback (q source freeSource)
      (phiDown.val.twist (descendOppositeHom source freeSource alpha).unop) =
        phiX.val.twist alpha.unop :=
    (CentralEllPrimeIBrFibreEquivariance.pullback_twist_of_commuting
      (q source freeSource) alpha.unop
      (descendOppositeHom source freeSource alpha).unop
      (descendOppositeHom_square source freeSource alpha) phiDown.val).trans
        (congrArg (fun chi : PrimeRegularClassFunction K X 2 => chi.twist alpha.unop) values)
  constructor
  · intro fixed
    apply Subtype.ext
    apply primeRegularClassFunction_pullback_injective_of_ker_card_coprime
      (q source freeSource) (q_surjective source freeSource)
      (Nat.prime_two.coprime_iff_not_dvd.mpr (q_kernel_primeToTwo source freeSource)).symm
    have fixedValues : phiX.val.twist alpha.unop = phiX.val :=
      congrArg Subtype.val fixed
    exact natural.trans (fixedValues.trans values.symm)
  · intro fixed
    apply Subtype.ext
    have fixedValues :
        phiDown.val.twist (descendOppositeHom source freeSource alpha).unop = phiDown.val :=
      congrArg Subtype.val fixed
    exact natural.symm.trans
      ((congrArg (PrimeRegularClassFunction.pullback (q source freeSource)) fixedValues).trans values)

/-- The original full upstairs inertia maps into the displayed downstairs ambient. -/
def inertiaHom : ActualAutAmbient rootX phiX →*
    ActualAutAmbient (rootDown source freeSource rootX) phiDown :=
  ((descendOppositeHom source freeSource).comp
    (MulAction.stabilizer (MulAut X)ᵐᵒᵖ phiX).subtype).codRestrict _ (by
      intro alpha
      exact (fixed_iff source freeSource rootX phiX phiDown values alpha.val).mp alpha.property)

theorem inertiaHom_injective :
    Function.Injective (inertiaHom source freeSource rootX phiX phiDown values) := by
  intro alpha beta same
  apply Subtype.ext
  apply descendOppositeHom_injective source freeSource
  exact congrArg Subtype.val same

/-- This is the actual subgroup to which the existing extension packet is restricted. -/
def inertiaImage : Subgroup (ActualAutAmbient (rootDown source freeSource rootX) phiDown) :=
  (inertiaHom source freeSource rootX phiX phiDown values).range

/-- The image is identified with the entire original upstairs inertia. -/
def inertiaImageEquiv : ActualAutAmbient rootX phiX ≃*
    inertiaImage source freeSource rootX phiX phiDown values :=
  MulEquiv.ofBijective
    (inertiaHom source freeSource rootX phiX phiDown values).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
      (inertiaHom_injective source freeSource rootX phiX phiDown values),
      MonoidHom.rangeRestrict_surjective _⟩

theorem inertiaHom_square (alpha : ActualAutAmbient rootX phiX) (x : X) :
    q source freeSource (alpha.val.unop x) =
      (inertiaHom source freeSource rootX phiX phiDown values alpha).val.unop
        (q source freeSource x) :=
  descendOppositeHom_square source freeSource alpha.val x

/-- The same square for the existing inverse-unop conjugation action. -/
theorem actualConjugation_square (alpha : ActualAutAmbient rootX phiX) (x : X) :
    q source freeSource (actualConjugation rootX phiX alpha x) =
      actualConjugation (rootDown source freeSource rootX) phiDown
        (inertiaHom source freeSource rootX phiX phiDown values alpha) (q source freeSource x) := by
  change q source freeSource (alpha.val.unop⁻¹ x) =
    (descendHom source freeSource alpha.val.unop)⁻¹ (q source freeSource x)
  rw [← (descendHom source freeSource).map_inv alpha.val.unop]
  exact (descendAutomorphism_apply_q source freeSource alpha.val.unop⁻¹ x).symm

/-- Both inner embeddings use the existing inverse-op convention. -/
theorem inertiaHom_inner (x : X) :
    inertiaHom source freeSource rootX phiX phiDown values (innerEmbedding rootX phiX x) =
      innerEmbedding (rootDown source freeSource rootX) phiDown (q source freeSource x) := by
  apply Subtype.ext
  change MulOpposite.op (descendHom source freeSource (MulAut.conj x⁻¹)) =
    MulOpposite.op (MulAut.conj ((q source freeSource x)⁻¹))
  rw [descendHom_conj, map_inv]

/-- The image ambient contains the same downstairs inner base. -/
theorem actualBase_le_inertiaImage :
    actualBase (rootDown source freeSource rootX) phiDown ≤
      inertiaImage source freeSource rootX phiX phiDown values := by
  intro a ha
  obtain ⟨y, rfl⟩ := ha
  obtain ⟨x, rfl⟩ := q_surjective source freeSource y
  exact ⟨innerEmbedding rootX phiX x,
    inertiaHom_inner source freeSource rootX phiX phiDown values x⟩

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionAutomorphisms


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
