import ModularRep.PaperProofs.TypeBRankThreePrincipalFieldMatchingSplitting
import ModularRep.PaperProofs.TypeBSemidirectFixedFieldFactorization
import ModularRep.PaperProofs.TypeBMatrixAmbientOrdinaryRoots

/-!
# The same principal correspondences under the actual SO and field ambient

The actions below are the existing principal-fibre restrictions of the
actual matrix ambient automorphisms. Their left-action convention pulls
back by the inverse actor. Specified GGGR and FYZ fixation put the whole
field factor in the character and weight-class inertias. The resulting
factorizations and matched full-ambient inertia equality concern these
literal subgroups, without fixing a raw weight representative.

The two equivariance theorems retain the already computed Omega map and
its SO orbit descent. No map, fixation or inertia equation is an input.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalAmbientFieldMatching

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalFieldNaturality TypeBRankThreePrincipalFieldMatchingSplitting
open TypeBRankThreePrincipalMatchedInertia TypeBGreenPrincipalConstituentSource
open TypeBCliffordOrthogonalAmbientQuotient TypeBCliffordOrthogonalAmbientActionBinding
open TypeBCliffordOrthogonalFullFieldBinding NavarroCoveringBrauerExtension
open TypeBCriterionHypotheses TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open CyclicOuterLemma37Concrete TypeBSemidirectFixedFieldFactorization

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section ActualActions

variable (F : Type) [Field F] [Finite F]
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (fieldSource : FieldActionSource 3 F r f parameters N)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "A" => OrthogonalAmbient 3 F parameters le_rfl N C fieldSource

/-- The actual matrix ambient acts on the prescribed Omega Brauer fibre. -/
def omegaBrauerAmbientAction : MulAction A (OmegaBrauer F root b) :=
  brauerFieldAction S literal root b hb (omegaAmbientAction fieldSource le_rfl C)

/-- The same actor acts on ordinary weight conjugacy classes in that block. -/
def omegaWeightAmbientAction : MulAction A (OmegaWeight F S b) :=
  weightFieldAction S literal b hb (omegaAmbientAction fieldSource le_rfl C)

def soBrauerAmbientAction : MulAction A (SOBrauer F rootH bH) :=
  brauerFieldAction SH literalH rootH bH hbH (soAmbientAction fieldSource le_rfl C)

def soWeightAmbientAction : MulAction A (SOWeight F SH bH) :=
  weightFieldAction SH literalH bH hbH (soAmbientAction fieldSource le_rfl C)

theorem omegaBrauerAmbientAction_val (a : A) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
    (a • theta).val = IrreducibleBrauerCharacter.twist root theta.val
      (omegaAmbientAction fieldSource le_rfl C a⁻¹) := rfl

theorem omegaWeightAmbientAction_val (a : A) (w : OmegaWeight F S b) :
    letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
    (a • w).val = CharacterWeight.rightTwistConjugacyClass
      (omegaAmbientAction fieldSource le_rfl C a⁻¹) w.val := rfl

theorem soBrauerAmbientAction_val (a : A) (Phi : SOBrauer F rootH bH) :
    letI := soBrauerAmbientAction F SH literalH rootH bH hbH parameters N fieldSource C
    (a • Phi).val = IrreducibleBrauerCharacter.twist rootH Phi.val
      (soAmbientAction fieldSource le_rfl C a⁻¹) := rfl

theorem soWeightAmbientAction_val (a : A) (v : SOWeight F SH bH) :
    letI := soWeightAmbientAction F SH literalH bH hbH parameters N fieldSource C
    (a • v).val = CharacterWeight.rightTwistConjugacyClass
      (soAmbientAction fieldSource le_rfl C a⁻¹) v.val := rfl

/-- The field inclusion uses precisely the inverse positive field actor. -/
theorem omegaAmbientInverse_inr (e : FieldGroup f) :
    omegaAmbientAction fieldSource le_rfl C ((SemidirectProduct.inr (φ := matrixField) e)⁻¹) =
      omegaFieldAction fieldSource le_rfl C e⁻¹ := by
  rw [← map_inv (SemidirectProduct.inr (φ := matrixField)) e, omegaAmbientAction_inr]

theorem soAmbientInverse_inr (e : FieldGroup f) :
    soAmbientAction fieldSource le_rfl C ((SemidirectProduct.inr (φ := matrixField) e)⁻¹) =
      matrixField e⁻¹ := by
  rw [← map_inv (SemidirectProduct.inr (φ := matrixField)) e, soAmbientAction_inr]

/-- The SO factor acts by its actual inverse inner automorphism. -/
theorem soAmbientInverse_inl (h : H F) :
    soAmbientAction fieldSource le_rfl C ((SemidirectProduct.inl (φ := matrixField) h)⁻¹) =
      MulAut.conj h⁻¹ := by
  rw [← map_inv (SemidirectProduct.inl (φ := matrixField)) h]
  exact SemidirectProduct.lift_inl _ _ _ h⁻¹

theorem omegaBrauerAmbientAction_inl (h : H F) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
    SemidirectProduct.inl (φ := matrixField) h • theta =
      brauerStep F S literal root b hb h theta := by
  apply Subtype.ext
  change inverseOpHom (matrixNaturalAction F parameters N fieldSource C).hom
      (SemidirectProduct.inl h) • theta.val = conjugationOp (G F) h • theta.val
  exact congrArg (fun alpha : (MulAut (G F))ᵐᵒᵖ => alpha • theta.val)
    (congrArg (fun rho => rho h) (matrixNaturalAction_on_SO F parameters N fieldSource C))

theorem omegaWeightAmbientAction_inl (h : H F) (w : OmegaWeight F S b) :
    letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
    SemidirectProduct.inl (φ := matrixField) h • w = weightStep F S literal b hb h w := by
  apply Subtype.ext
  change inverseOpHom (matrixNaturalAction F parameters N fieldSource C).hom
      (SemidirectProduct.inl h) • w.val = conjugationOp (G F) h • w.val
  exact congrArg (fun alpha : (MulAut (G F))ᵐᵒᵖ => alpha • w.val)
    (congrArg (fun rho => rho h) (matrixNaturalAction_on_SO F parameters N fieldSource C))

theorem soBrauerAmbientAction_inl_fixed (h : H F) (Phi : SOBrauer F rootH bH) :
    letI := soBrauerAmbientAction F SH literalH rootH bH hbH parameters N fieldSource C
    SemidirectProduct.inl (φ := matrixField) h • Phi = Phi := by
  apply Subtype.ext
  change IrreducibleBrauerCharacter.twist rootH Phi.val
      (soAmbientAction fieldSource le_rfl C ((SemidirectProduct.inl h)⁻¹)) = Phi.val
  rw [soAmbientInverse_inl F parameters N fieldSource C h]
  exact CyclicOuterLemma37Concrete.inner_fixes_ibr rootH h Phi.val

theorem soWeightAmbientAction_inl_fixed (h : H F) (v : SOWeight F SH bH) :
    letI := soWeightAmbientAction F SH literalH bH hbH parameters N fieldSource C
    SemidirectProduct.inl (φ := matrixField) h • v = v := by
  apply Subtype.ext
  change CharacterWeight.rightTwistConjugacyClass
      (soAmbientAction fieldSource le_rfl C ((SemidirectProduct.inl h)⁻¹)) v.val = v.val
  rw [soAmbientInverse_inl F parameters N fieldSource C h]
  exact CyclicOuterLemma37Concrete.inner_fixes_weightClass h v.val

end ActualActions

section PrincipalSources

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] {r f : ℕ} [CharP F r]
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  {S : OmegaWeightSource (k := k) (K := K) F}
  {SH : SOWeightSource (k := k) (K := K) F}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
  {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
  {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
  {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
  {literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val}
  {indexTwo : (G F).index = 2}
  {parameters : OddFieldParameters F r f} {N : NormSource 3 F}
  {fieldSource : FieldActionSource 3 F r f parameters N}
  {C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N}
  {Msys : ModularSystem 2 K O k}
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb indexTwo)
  (roots : TypeBGreenPrincipalConstituentSource.RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  (fyz : TypeBRankThreePrincipalWeightFieldSplitting.FYZCorollary363SplittingSource
    F r f parameters Msys coefficient root rootH
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys root rootCalibration)
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys rootH rootHCalibration)
    S SH literal literalH guard guardH b hb bH hbH)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C
local notation "A" => OrthogonalAmbient 3 F parameters le_rfl N C fieldSource

include gggr in
theorem omegaBrauerAmbientAction_inr_fixed (e : FieldGroup f) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
    SemidirectProduct.inr (φ := matrixField) e • theta = theta := by
  apply Subtype.ext
  change IrreducibleBrauerCharacter.twist root theta.val
      (omegaAmbientAction fieldSource le_rfl C ((SemidirectProduct.inr e)⁻¹)) = theta.val
  rw [omegaAmbientInverse_inr F parameters N fieldSource C e]
  exact congrArg Subtype.val (omegaBrauerFieldTwist_fixed gggr e⁻¹ theta)

include fyz in
theorem omegaWeightAmbientAction_inr_fixed (e : FieldGroup f) (w : OmegaWeight F S b) :
    letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
    SemidirectProduct.inr (φ := matrixField) e • w = w := by
  apply Subtype.ext
  change CharacterWeight.rightTwistConjugacyClass
      (omegaAmbientAction fieldSource le_rfl C ((SemidirectProduct.inr e)⁻¹)) w.val = w.val
  rw [omegaAmbientInverse_inr F parameters N fieldSource C e]
  exact congrArg Subtype.val (omegaWeightFieldTwist_fixed
    (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration) fyz e⁻¹ w)

include gggr roots fieldScope green principalLift clifford principalRestriction in
theorem soBrauerAmbientAction_inr_fixed (e : FieldGroup f) (Phi : SOBrauer F rootH bH) :
    letI := soBrauerAmbientAction F SH literalH rootH bH hbH parameters N fieldSource C
    SemidirectProduct.inr (φ := matrixField) e • Phi = Phi := by
  apply Subtype.ext
  change IrreducibleBrauerCharacter.twist rootH Phi.val
      (soAmbientAction fieldSource le_rfl C ((SemidirectProduct.inr e)⁻¹)) = Phi.val
  rw [soAmbientInverse_inr F parameters N fieldSource C e]
  exact congrArg Subtype.val (soBrauerFieldTwist_fixed (literalH := literalH) (hbH := hbH) gggr roots
    fieldScope green principalLift clifford principalRestriction e⁻¹ Phi)

include fyz in
theorem soWeightAmbientAction_inr_fixed (e : FieldGroup f) (v : SOWeight F SH bH) :
    letI := soWeightAmbientAction F SH literalH bH hbH parameters N fieldSource C
    SemidirectProduct.inr (φ := matrixField) e • v = v := by
  apply Subtype.ext
  change CharacterWeight.rightTwistConjugacyClass
      (soAmbientAction fieldSource le_rfl C ((SemidirectProduct.inr e)⁻¹)) v.val = v.val
  rw [soAmbientInverse_inr F parameters N fieldSource C e]
  exact congrArg Subtype.val (soWeightFieldTwist_fixed
    (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration) fyz e⁻¹ v)

include gggr in
/-- The actual field subgroup lies in the full character inertia. -/
theorem omegaBrauerInertia_inr_le (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    embeddedE matrixField ≤ brauerInertia (G F) matrixField matrixAction root theta.val := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  rintro _ ⟨e, rfl⟩
  change inverseOpHom (matrixNaturalAction F parameters N fieldSource C).hom
    (SemidirectProduct.inr e) • theta.val = theta.val
  exact congrArg Subtype.val (omegaBrauerAmbientAction_inr_fixed gggr e theta)

include fyz in
/-- This is containment in a weight-CLASS inertia, not a raw-pair inertia. -/
theorem omegaWeightClassInertia_inr_le (w : OmegaWeight F S b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    embeddedE matrixField ≤ weightClassInertia (G F) matrixField matrixAction w.val := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  rintro _ ⟨e, rfl⟩
  change inverseOpHom (matrixNaturalAction F parameters N fieldSource C).hom
    (SemidirectProduct.inr e) • w.val = w.val
  exact congrArg Subtype.val (omegaWeightAmbientAction_inr_fixed
    (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration) fyz e w)

include gggr in
/-- The literal criterion character-inertia product is now a deduction. -/
theorem omegaBrauerInertia_factorization (theta : OmegaBrauer F root b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    BrauerFactorization (G F) matrixField matrixAction root theta.val := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact subgroup_eq_product_of_inr_le matrixField
    (brauerInertia (G F) matrixField matrixAction root theta.val)
    (omegaBrauerInertia_inr_le gggr theta)

include fyz in
/-- The corresponding product uses the two canonical factors in the same
ambient and the full inertia of the supplied principal weight class. -/
theorem omegaWeightClassInertia_factorization (w : OmegaWeight F S b) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    (weightClassInertia (G F) matrixField matrixAction w.val : Set A) =
      (factorInertia matrixField (weightClassInertia (G F) matrixField matrixAction w.val)
        (embeddedM matrixField) : Set A) *
      (factorInertia matrixField (weightClassInertia (G F) matrixField matrixAction w.val)
        (embeddedE matrixField) : Set A) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  exact subgroup_eq_product_of_inr_le matrixField
    (weightClassInertia (G F) matrixField matrixAction w.val)
    (omegaWeightClassInertia_inr_le (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration) fyz w)

variable
  {delta : H F} {outside : delta ∉ G F} {notThree : Nat.card F ≠ 3}
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta indexTwo outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)

local notation "omegaMap" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "omegaDelta" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv_delta covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction

include gggr fyz in
/-- Full actual SO/field equivariance of precisely the accepted Omega map. -/
theorem principalOmegaEquiv_ambient (a : A) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
    letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
    omegaMap (a • theta) = a • omegaMap theta := by
  letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
  letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
  apply equivariant_of_inl_of_inr_fixed matrixField omegaMap _ _ _ a theta
  · intro h x
    rw [omegaBrauerAmbientAction_inl F S literal root b hb parameters N fieldSource C,
      omegaWeightAmbientAction_inl F S literal b hb parameters N fieldSource C]
    exact TypeBRankThreePrincipalOrbitBinding.seed_H_equivariant
      F S literal root b hb delta indexTwo outside omegaMap omegaDelta h x
  · intro e x
    exact omegaBrauerAmbientAction_inr_fixed gggr e x
  · intro e w
    exact omegaWeightAmbientAction_inr_fixed (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration) fyz e w

include gggr fyz in
/-- The same full actor also respects the accepted SO orbit descent. -/
theorem principalSOEquiv_ambient (a : A) (Phi : SOBrauer F rootH bH) :
    letI := soBrauerAmbientAction F SH literalH rootH bH hbH parameters N fieldSource C
    letI := soWeightAmbientAction F SH literalH bH hbH parameters N fieldSource C
    soMap (a • Phi) = a • soMap Phi := by
  letI := soBrauerAmbientAction F SH literalH rootH bH hbH parameters N fieldSource C
  letI := soWeightAmbientAction F SH literalH bH hbH parameters N fieldSource C
  apply equivariant_of_inl_of_inr_fixed matrixField soMap _ _ _ a Phi
  · intro h x
    rw [soBrauerAmbientAction_inl_fixed F SH literalH rootH bH hbH parameters N fieldSource C,
      soWeightAmbientAction_inl_fixed F SH literalH bH hbH parameters N fieldSource C]
  · intro e x
    exact soBrauerAmbientAction_inr_fixed (literalH := literalH) gggr roots fieldScope green
      principalLift clifford principalRestriction e x
  · intro e v
    exact soWeightAmbientAction_inr_fixed (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration) fyz e v

include gggr fyz in
/-- Every literal constituent/covered-class pair from the same SO map has
equal FULL ambient inertias. No chosen raw representative is fixed here. -/
theorem principalSOEquiv_matched_ambient_inertia_eq
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val) :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    brauerInertia (G F) matrixField matrixAction root theta.val =
      weightClassInertia (G F) matrixField matrixAction w.val := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  apply subgroup_eq_of_inl_comap_eq_of_inr_le matrixField
    (brauerInertia (G F) matrixField matrixAction root theta.val)
    (weightClassInertia (G F) matrixField matrixAction w.val)
    (omegaBrauerInertia_inr_le gggr theta)
    (omegaWeightClassInertia_inr_le (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration) fyz w)
  exact TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv_matched_criterion_inertia_eq
    covering counts roots fieldScope green principalLift clifford principalRestriction
    N fieldSource C Phi theta w occurs covered

end PrincipalSources

end ModularRep.PaperProofs.TypeBRankThreePrincipalAmbientFieldMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
