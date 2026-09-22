import ModularRep.PaperProofs.TypeBRankThreePrincipalCoveredInertia
import ModularRep.PaperProofs.TypeBCriterionHypotheses
import ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientActionBinding

/-!
# Principal matched inertia on the literal SO criterion factor

The actual occurrence/covering anchor of the constructed SO correspondence
discharges the two-cover hypothesis of the checked class-inertia theorem.
The result remains on principal fibres and weight conjugacy classes.

The criterion's natural action is constructed from the existing actual
SO/field semidirect action. Its restriction to SO is the same opposite
conjugation action, so the criterion's M-factor inertias are identified
with the literal character and weight-class inertias. Products use the
same actual Hall preimage in SO. No all-pairs condition, full-automorphism
identification, raw inertia or extension/triple predicate is asserted.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalMatchedInertia

open ModularRep CharacterWeight TypeBCliffordCarriers
open TypeBCentralKernelCarriers TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalOvergroupMatching
open TypeBRankThreePrincipalCoveredInertia TypeBGreenPrincipalConstituentSource
open NavarroCoveringBrauerExtension
open TypeBCliffordOrthogonalAmbientQuotient TypeBCliffordOrthogonalAmbientActionBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable (F : Type) [Field F] [Finite F]
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (delta : H F) (indexTwo : (G F).index = 2) (outside : delta ∉ G F)
  {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  [Fintype (OmegaWeight F S b)] [DecidableEq (SOWeight F SH bH)]
  (dgn : WeightCoveringModel (k := k) (K := K) F)
  (covering : PublishedWeightCovering F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn)
  (seed : OmegaBrauer F root b ≃ OmegaWeight F S b)
  (seed_delta : ∀ theta,
    seed (brauerPermutation F S literal root b hb delta indexTwo theta) =
      weightPermutation F S literal b hb delta indexTwo (seed theta))
  (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

/-- Every actual constituent and every class covered by its constructed
SO partner have equal literal SO inertias, on the principal domain. -/
theorem matched_classInertia_eq (Phi : SOBrauer F rootH bH)
    (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSource.CoversClass (G F) dgn
      (overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
        green principalLift clifford principalRestriction Phi).val w.val) :
    classInertia F S b w = T (G F) root theta.val :=
  coversClass_inertia_eq F S literal b hb delta indexTwo SH bH parameters notThree
    outside hbH literalH dgn covering root seed seed_delta theta
    (overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
      green principalLift clifford principalRestriction Phi) w
    ((occurs_iff_coversClass F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
      green principalLift clifford principalRestriction Phi theta).mp occurs) covered

/-- The SAME literal Hall subgroup of SO/Omega supplies both preimages. -/
theorem matched_hall_product_eq (hall : TypeBCriterionHypotheses.HallData (G F) 2)
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSource.CoversClass (G F) dgn
      (overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
        green principalLift clifford principalRestriction Phi).val w.val) :
    (T (G F) root theta.val : Set (H F)) * (hall.preimage : Set (H F)) =
      (classInertia F S b w : Set (H F)) * (hall.preimage : Set (H F)) := by
  rw [matched_classInertia_eq F S literal root b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
    green principalLift clifford principalRestriction Phi theta w occurs covered]

section ActualMatrixAmbient

variable (N : NormSource 3 F)
  (fieldSource : FieldActionSource 3 F r f parameters N)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F r f parameters (Nat.le_refl 3) N)

/-- The criterion's natural action is the already constructed literal
SO/field action on the actual commutator subgroup. -/
def matrixNaturalAction : TypeBCriterionHypotheses.NaturalAction (G F)
    (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource) where
  hom := omegaAmbientAction fieldSource (Nat.le_refl 3) orthogonal
  value := fun _ _ => rfl

/-- Restriction to the actual SO factor agrees pointwise with its original
conjugation action on the literal subgroup. -/
theorem matrixNaturalAction_inl (h : H F) :
    (matrixNaturalAction F parameters N fieldSource orthogonal).hom
        (SemidirectProduct.inl h) = originalAction (G F) h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change h * soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource
      1 x.val * h⁻¹ = h * x.val * h⁻¹
  rw [map_one]
  rfl

/-- The criterion and the existing inertia library use the same inverse
and opposite action conventions on the SO factor. -/
theorem matrixNaturalAction_on_SO :
    (CyclicOuterLemma37Concrete.inverseOpHom
      (matrixNaturalAction F parameters N fieldSource orthogonal).hom).comp
        SemidirectProduct.inl = conjugationOp (G F) := by
  apply MonoidHom.ext
  intro h
  change MulOpposite.op
      ((matrixNaturalAction F parameters N fieldSource orthogonal).hom
        ((SemidirectProduct.inl h)⁻¹)) =
    MulOpposite.op (originalAction (G F) h⁻¹)
  rw [← map_inv]
  exact congrArg MulOpposite.op
    (matrixNaturalAction_inl F parameters N fieldSource orthogonal h⁻¹)

theorem matrix_brauerMInertia_eq (theta : OmegaBrauer F root b) :
    TypeBCriterionHypotheses.brauerMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) root theta.val =
        T (G F) root theta.val := by
  change (MulAction.stabilizer (MulAut (G F))ᵐᵒᵖ theta.val).comap
    ((CyclicOuterLemma37Concrete.inverseOpHom
      (matrixNaturalAction F parameters N fieldSource orthogonal).hom).comp
        SemidirectProduct.inl) = _
  rw [matrixNaturalAction_on_SO]
  rfl

theorem matrix_weightMInertia_eq (w : OmegaWeight F S b) :
    TypeBCriterionHypotheses.weightMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) w.val =
        classInertia F S b w := by
  change (MulAction.stabilizer (MulAut (G F))ᵐᵒᵖ w.val).comap
    ((CyclicOuterLemma37Concrete.inverseOpHom
      (matrixNaturalAction F parameters N fieldSource orthogonal).hom).comp
        SemidirectProduct.inl) = _
  rw [matrixNaturalAction_on_SO]
  rfl

/-- Principal matched inertia equality expressed in the criterion's actual
M-factor carriers for matrix SO semidirect the displayed field group. -/
theorem matched_criterion_inertia_eq (Phi : SOBrauer F rootH bH)
    (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSource.CoversClass (G F) dgn
      (overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
        green principalLift clifford principalRestriction Phi).val w.val) :
    TypeBCriterionHypotheses.brauerMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) root theta.val =
    TypeBCriterionHypotheses.weightMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) w.val := by
  rw [matrix_brauerMInertia_eq F root b parameters N fieldSource orthogonal theta,
    matrix_weightMInertia_eq F S b parameters N fieldSource orthogonal w]
  exact (matched_classInertia_eq F S literal root b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
    green principalLift clifford principalRestriction Phi theta w occurs covered).symm

/-- The required same-Hall product on matched principal pairs. This is
not the criterion's all-IBr/all-weight predicate. -/
theorem matched_criterion_hall_product_eq
    (hall : TypeBCriterionHypotheses.HallData (G F) 2)
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSource.CoversClass (G F) dgn
      (overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
        green principalLift clifford principalRestriction Phi).val w.val) :
    (TypeBCriterionHypotheses.brauerMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) root theta.val : Set (H F)) *
        (hall.preimage : Set (H F)) =
    (TypeBCriterionHypotheses.weightMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) w.val : Set (H F)) *
        (hall.preimage : Set (H F)) := by
  rw [matched_criterion_inertia_eq F S literal root b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
    green principalLift clifford principalRestriction N fieldSource orthogonal
    Phi theta w occurs covered]

end ActualMatrixAmbient

end ModularRep.PaperProofs.TypeBRankThreePrincipalMatchedInertia



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
