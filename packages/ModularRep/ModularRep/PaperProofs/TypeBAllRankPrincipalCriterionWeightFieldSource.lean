import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionCarriers
import ModularRep.PaperProofs.TypeBRankThreePrincipalWeightFieldBinding
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionFixedBlockSource

/-!
# Principal weight-class field fixation in every assigned odd dimension

The two source fields are exactly the generator specializations of FYZ,
Corollary 3.63 (author TeX 2281--2292), on the actual SO and Omega principal
ordinary weight classes. The generator is the coordinate defining-prime
Frobenius of lines 2258--2259. The same modular system, prescribed root
calibrations, specified block operations and sufficient ordinary roots are
retained. Their specified/source realization remains E2/U; no source
inhabitant is constructed here.

The specified calibration is the same principal-block-scoped object used
by the fixed-block criterion. Its literal field supplies the catalogue
identity; no separate all-weight local reduction guard is required.

The full positive and inverse field conclusions are deductions using the
existing coordinate-power equations and generic fixed-powers lemma. The
norm, orthogonal projection and Clifford field source are the same indices
as the principal criterion carriers. Neither raw representative fixation,
Brauer fixation, a matching, nor a criterion is a source field. Ordinary
algebraic closure is not required.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionWeightFieldSource

open ModularRep CharacterWeight TypeBCliffordCarriers
open TypeBCentralKernelBlockSource
open TypeBLocalReductionInstantiation TypeBOrthogonalFieldAutomorphism
open TypeBAllRankPrincipalCriterionCarriers
open TypeBAllRankPrincipalCriterionFixedBlockSource

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T

local instance omegaOrdinaryRoots {n : ℕ} {F K : Type}
    [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H n F))] :
    HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G n F))

/-- Narrow all-rank FYZ Corollary 3.63 source on the two actual principal
ordinary weight-class fibres. All ambient, coefficient and local block
calibrations precede the two published generator conclusions. -/
structure FYZCorollary363Source
    {n r f : ℕ} (F : Type) [Field F] [Finite F] [CharP F r]
    (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
    (N : NormSource n F)
    (C : TypeBCliffordOrthogonalSourceBinding.Source
      n F r f parameters (rank3 rank) N)
    (fieldSource : FieldActionSource n F r f parameters N)
    {k K O : Type}
    [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
    [CharP k 2] [IsAlgClosed k] [CharZero K]
    (Msys : ModularSystem 2 K O k)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (H n F))]
    (coefficient : SpathCoefficientField 2 k Msys.prime)
    (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
    (rootH : PrimeRegularRootEmbedding 2 k K (H n F))
    (compatibleX : RootResidueCompatible Msys rootX)
    (compatibleH : RootResidueCompatible Msys rootH)
    (SX : TypeBQ3PrincipalWeightInflation.CoverWeightSource
      (k := k) (K := K) (X n F))
    (SH : TypeBQ3PrincipalWeightInflation.CoverWeightSource
      (k := k) (K := K) (H n F))
    (bX : LiteralPrimitiveBlock k (X n F)) (principalX : IsPrincipal bX)
    (bH : LiteralPrimitiveBlock k (H n F)) (principalH : IsPrincipal bH)
    (calibrationX : PhysicalWeightCalibration Msys rootX SX bX)
    (calibrationH : PhysicalWeightCalibration Msys rootH SH bH) : Prop where
  omega_generator : ∀ w : SX.Fibre bX,
    CharacterWeight.rightTwistConjugacyClass
      (primeFrobeniusOmega n F r parameters.prime) w.val = w.val
  so_generator : ∀ w : SH.Fibre bH,
    CharacterWeight.rightTwistConjugacyClass
      (primeFrobeniusSpecialOrthogonal n F r parameters.prime) w.val = w.val

section FullField

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}
  {N : NormSource n F}
  {C : TypeBCliffordOrthogonalSourceBinding.Source
    n F r f parameters (rank3 rank) N}
  {fieldSource : FieldActionSource n F r f parameters N}
  {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  {Msys : ModularSystem 2 K O k}
  [HasEnoughRootsOfUnity K (Nat.card (H n F))]
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  {rootX : PrimeRegularRootEmbedding 2 k K (X n F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H n F)}
  {compatibleX : RootResidueCompatible Msys rootX}
  {compatibleH : RootResidueCompatible Msys rootH}
  {SX : TypeBQ3PrincipalWeightInflation.CoverWeightSource
    (k := k) (K := K) (X n F)}
  {SH : TypeBQ3PrincipalWeightInflation.CoverWeightSource
    (k := k) (K := K) (H n F)}
  {bX : LiteralPrimitiveBlock k (X n F)} {principalX : IsPrincipal bX}
  {bH : LiteralPrimitiveBlock k (H n F)} {principalH : IsPrincipal bH}
  {calibrationX : PhysicalWeightCalibration Msys rootX SX bX}
  {calibrationH : PhysicalWeightCalibration Msys rootH SH bH}
  (source : FYZCorollary363Source F parameters rank N C fieldSource Msys coefficient
    rootX rootH compatibleX compatibleH SX SH bX principalX bH principalH
    calibrationX calibrationH)

include source in
/-- Every element of the same actual Omega field action fixes the class. -/
theorem omega_field_fixed (e : FieldGroup f) (w : SX.Fibre bX) :
    CharacterWeight.rightTwistConjugacyClass
      (omegaAction parameters rank N C fieldSource e) w.val = w.val := by
  rw [omegaAction_eq_prime_pow parameters rank N C fieldSource e]
  exact TypeBRankThreePrincipalWeightFieldBinding.rightTwist_pow_fixed
    (primeFrobeniusOmega n F r parameters.prime) w.val
    (source.omega_generator w) e.toAdd.val

include source in
/-- Every element of the same actual SO field action fixes the class. -/
theorem so_field_fixed (e : FieldGroup f) (w : SH.Fibre bH) :
    CharacterWeight.rightTwistConjugacyClass
      (fieldAction parameters rank N C fieldSource e) w.val = w.val := by
  rw [fieldAction_eq_prime_pow parameters rank N C fieldSource e]
  exact TypeBRankThreePrincipalWeightFieldBinding.rightTwist_pow_fixed
    (primeFrobeniusSpecialOrthogonal n F r parameters.prime) w.val
    (source.so_generator w) e.toAdd.val

include source in
/-- The inverse convention uses the inverse of the same field-group element. -/
theorem omega_inverse_field_fixed (e : FieldGroup f) (w : SX.Fibre bX) :
    CharacterWeight.rightTwistConjugacyClass
      (omegaAction parameters rank N C fieldSource e⁻¹) w.val = w.val :=
  omega_field_fixed source e⁻¹ w

include source in
/-- The same inverse-field conclusion for the actual SO class. -/
theorem so_inverse_field_fixed (e : FieldGroup f) (w : SH.Fibre bH) :
    CharacterWeight.rightTwistConjugacyClass
      (fieldAction parameters rank N C fieldSource e⁻¹) w.val = w.val :=
  so_field_fixed source e⁻¹ w

end FullField

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionWeightFieldSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
