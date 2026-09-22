import ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitCount
import ModularRep.PaperProofs.TypeBRankThreePrincipalOvergroupMatching
import ModularRep.PaperProofs.TypeBRankThreePrincipalMatchedInertia

/-!
# Principal seed and SO correspondence from the derived orbit count

The old numerical Clifford-orbit adapter is constructed from the actual
constituent correspondence and quotient action. The existing independent
principal counts and specified ordinary-weight covering data then feed
the checked C2 construction. Neither an orbit-count source nor a seed
correspondence is an input to the resulting Omega and SO maps.

The SO map uses precisely the chosen constructed Omega seed, with literal
restriction occurrence and ordinary covering anchors. All inherited
Green/Clifford/principal, numerical and specified source realizations are
still explicit. No field-equivariance, extension or triple is supplied.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalCountApplication

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding TypeBGreenPrincipalConstituentSource
open TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBRankThreePrincipalOvergroupMatching NavarroCoveringBrauerExtension
open TypeBRankThreePrincipalMatchedInertia TypeBCliffordOrthogonalAmbientQuotient

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable (F : Type) [Field F] [Finite F]
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (delta : H F) (indexTwo : (G F).index = 2)
  {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
  (outside : delta ∉ G F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

/-- The former orbit-count input is now constructed, using its exact
constituent-level proof on these same supported characters. -/
def principalCliffordOrbitCount :
    PrincipalCliffordOrbitCount F S literal root b hb delta indexTwo
      SH rootH bH parameters notThree outside hbH literalH where
  orbit_count := TypeBRankThreePrincipalOrbitCount.principal_orbit_count
    F S literal root b hb delta indexTwo outside rootH bH hbH roots fieldScope
    green principalLift clifford principalRestriction

variable
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)
  (dgn : WeightCoveringModel (k := k) (K := K) F)
  (covering : PublishedWeightCovering F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn)

include green principalLift clifford principalRestriction counts covering in
/-- The actual principal seed is derived without a supplied orbit count
or correspondence. The existing C2 theorem is reused unchanged. -/
theorem exists_principalOmega_equivariantEquiv :
    ∃ seed : OmegaBrauer F root b ≃ OmegaWeight F S b,
      ∀ theta,
        seed (brauerPermutation F S literal root b hb delta indexTwo theta) =
          weightPermutation F S literal b hb delta indexTwo (seed theta) :=
  TypeBRankThreePrincipalCountBinding.principalOmega_equivariantEquiv
    F S literal root b hb delta indexTwo parameters notThree outside SH literalH rootH bH hbH
    counts
    (principalCliffordOrbitCount F S literal root b hb delta indexTwo parameters notThree
      outside SH literalH rootH bH hbH roots fieldScope green principalLift clifford
      principalRestriction)
    dgn covering

/-- One fixed seed from the checked construction, retained in every
subsequent SO anchor. -/
def principalOmegaEquiv : OmegaBrauer F root b ≃ OmegaWeight F S b :=
  Classical.choose (exists_principalOmega_equivariantEquiv F S literal root b hb delta
    indexTwo parameters notThree outside SH literalH rootH bH hbH roots fieldScope green
    principalLift clifford principalRestriction counts dgn covering)

theorem principalOmegaEquiv_delta (theta : OmegaBrauer F root b) :
    principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering (brauerPermutation F S literal root b hb delta indexTwo theta) =
    weightPermutation F S literal b hb delta indexTwo
      (principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree outside
        SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
        counts dgn covering theta) :=
  Classical.choose_spec (exists_principalOmega_equivariantEquiv F S literal root b hb delta
    indexTwo parameters notThree outside SH literalH rootH bH hbH roots fieldScope green
    principalLift clifford principalRestriction counts dgn covering) theta

/-- The SO equivalence uses the same constructed seed and no supplied
overgroup correspondence. -/
def principalSOEquiv : SOBrauer F rootH bH ≃ SOWeight F SH bH :=
  overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering
    (principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    (principalOmegaEquiv_delta F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    rootH roots fieldScope green principalLift clifford principalRestriction

theorem principalSOEquiv_principalAbove (theta : OmegaBrauer F root b) :
    principalSOEquiv F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering
      (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift theta) =
    covering.cover (principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree
      outside SH literalH rootH bH hbH roots fieldScope green principalLift clifford
      principalRestriction counts dgn covering theta) :=
  overgroupEquiv_principalAbove F S literal root b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering
    (principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    (principalOmegaEquiv_delta F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    rootH roots fieldScope green principalLift clifford principalRestriction theta

/-- Actual occurrence is literal covering for the SO map derived from
the original independent sources, on every supported constituent. -/
theorem principalSOEquiv_occurs_iff_coversClass
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ↔
      TypeBWeightCoveringSource.CoversClass (G F) dgn
        (principalSOEquiv F S literal root b hb delta indexTwo parameters notThree outside
          SH literalH rootH bH hbH roots fieldScope green principalLift clifford
          principalRestriction counts dgn covering Phi).val
        (principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree outside
          SH literalH rootH bH hbH roots fieldScope green principalLift clifford
          principalRestriction counts dgn covering theta).val :=
  occurs_iff_coversClass F S literal root b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering
    (principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    (principalOmegaEquiv_delta F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    rootH roots fieldScope green principalLift clifford principalRestriction Phi theta

/-- Matched principal J-products for the SO correspondence constructed
from the independent sources. No seed, orbit count, SO map or J predicate
is supplied to this endpoint. Both inertias use the actual matrix
semidirect action, and both products use the same literal Hall preimage. -/
theorem principalSOEquiv_matched_criterion_hall_product_eq
    (N : NormSource 3 F)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
      3 F r f parameters (Nat.le_refl 3) N)
    (hall : TypeBCriterionHypotheses.HallData (G F) 2)
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b)
    (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSource.CoversClass (G F) dgn
      (principalSOEquiv F S literal root b hb delta indexTwo parameters notThree outside
        SH literalH rootH bH hbH roots fieldScope green principalLift clifford
        principalRestriction counts dgn covering Phi).val w.val) :
    (TypeBCriterionHypotheses.brauerMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) root theta.val : Set (H F)) *
        (hall.preimage : Set (H F)) =
    (TypeBCriterionHypotheses.weightMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) w.val : Set (H F)) *
        (hall.preimage : Set (H F)) :=
  matched_criterion_hall_product_eq F S literal root b hb delta indexTwo outside parameters
    notThree SH literalH bH hbH dgn covering
    (principalOmegaEquiv F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    (principalOmegaEquiv_delta F S literal root b hb delta indexTwo parameters notThree outside
      SH literalH rootH bH hbH roots fieldScope green principalLift clifford principalRestriction
      counts dgn covering)
    rootH roots fieldScope green principalLift clifford principalRestriction N fieldSource
    orthogonal hall Phi theta w occurs covered

end ModularRep.PaperProofs.TypeBRankThreePrincipalCountApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
