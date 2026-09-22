import ModularRep.PaperProofs.TypeBRankThreePrincipalSOMatchingSplitting
import ModularRep.PaperProofs.TypeBRankThreePrincipalFieldNaturality
import ModularRep.PaperProofs.TypeBRankThreePrincipalWeightFieldSplitting
import ModularRep.PaperProofs.TypeBRankThreePrincipalGGGRInputs
import ModularRep.PaperProofs.TypeBSpinSOOrdinaryRoots

/-!
# Field equivariance of the same principal Omega and SO correspondences

The specified GGGR inputs fix the prescribed Omega Brauer fibre. Green's
surjective principal-above map and its field naturality then fix the SO
Brauer fibre. FYZ supplies the two ordinary weight-class fixation results.
These deductions give field equivariance of precisely the already chosen
count-derived Omega map and its SO orbit descent, with no new map choice.

Spin finiteness and sufficient ordinary roots are constructed from the
actual Spin projection and the actual index-two Omega inclusion in SO.
The positive twists and the inverse-actor left actions remain distinct.
No raw-weight fixation, extension or individual-triple claim is made.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalFieldMatchingSplitting

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalBrauerOrbitBinding TypeBRankThreePrincipalFieldNaturality
open TypeBGreenPrincipalConstituentSource NavarroCoveringBrauerExtension
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {r f : ℕ} [CharP F r]
  [HasEnoughRootsOfUnity K (Nat.card (H F))]

/-- The existing GGGR package on the exact specified decomposition of S.
Its Spin instances are deductions in the same coefficient field. -/
abbrev GGGRInputs
    (S : OmegaWeightSource (k := k) (K := K) F)
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (Msys : ModularSystem 2 K O k)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
    (root : PrimeRegularRootEmbedding 2 k K (G F))
    (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
    (indexTwo : (G F).index = 2) :=
  letI : Finite (Spin 3 F N) :=
    TypeBSpinSOOrdinaryRoots.spinFinite N parameters le_rfl C indexTwo
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N)) :=
    TypeBSpinSOOrdinaryRoots.spinOrdinaryRoots N parameters le_rfl C indexTwo
  letI := S.operations.ambientBlockData.fintypeBlock
  TypeBRankThreePrincipalGGGRInputs.Inputs parameters fieldSource Msys C root
    (physicalDecomposition S literal) b hb

variable
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

include gggr in
/-- Specified GGGR fixation restricted to the same supported Omega fibre. -/
theorem omegaBrauerFieldTwist_fixed (e : FieldGroup f) (theta : OmegaBrauer F root b) :
    omegaBrauerFieldTwist F S literal root b hb parameters N fieldSource C e theta = theta := by
  letI : Finite (Spin 3 F N) :=
    TypeBSpinSOOrdinaryRoots.spinFinite N parameters le_rfl C indexTwo
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N)) :=
    TypeBSpinSOOrdinaryRoots.spinOrdinaryRoots N parameters le_rfl C indexTwo
  letI := S.operations.ambientBlockData.fintypeBlock
  apply Subtype.ext
  exact TypeBRankThreePrincipalGGGRInputs.matrixPrincipalBrauer_fixed
    parameters fieldSource Msys C root (physicalDecomposition S literal) b hb
    gggr e theta.val theta.property

variable
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

include gggr roots fieldScope green principalLift clifford principalRestriction in
/-- Every principal SO character is above a fixed Omega constituent, and
the very same principal-above map commutes with the field twist. -/
theorem soBrauerFieldTwist_fixed (e : FieldGroup f) (Phi : SOBrauer F rootH bH) :
    soBrauerFieldTwist F SH literalH rootH bH hbH parameters N fieldSource C e Phi = Phi := by
  obtain ⟨theta, rfl⟩ := principalAbove_surjective F root b hb rootH bH hbH
    roots fieldScope indexTwo green principalLift clifford principalRestriction Phi
  exact
    (principalAbove_fieldTwist F S literal root b hb SH literalH rootH bH hbH
      parameters N fieldSource C roots fieldScope indexTwo green principalLift e theta).symm.trans
      (congrArg
        (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift)
        (omegaBrauerFieldTwist_fixed gggr e theta))

variable
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

include fyz in
/-- FYZ fixation concerns the actual Omega ordinary weight conjugacy class. -/
theorem omegaWeightFieldTwist_fixed (e : FieldGroup f) (w : OmegaWeight F S b) :
    omegaWeightFieldTwist F S literal b hb parameters N fieldSource C e w = w := by
  apply Subtype.ext
  exact TypeBRankThreePrincipalWeightFieldSplitting.omega_field_fixed fyz fieldSource le_rfl C e w

include fyz in
/-- The corresponding SO weight-class fixation uses the same field actor. -/
theorem soWeightFieldTwist_fixed (e : FieldGroup f) (v : SOWeight F SH bH) :
    soWeightFieldTwist F SH literalH bH hbH parameters N fieldSource C e v = v := by
  apply Subtype.ext
  exact TypeBRankThreePrincipalWeightFieldSplitting.so_field_fixed fyz fieldSource le_rfl C e v

include gggr in
theorem omegaBrauerFieldAction_fixed (e : FieldGroup f) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerFieldAction F S literal root b hb parameters N fieldSource C
    e • theta = theta :=
  omegaBrauerFieldTwist_fixed gggr e⁻¹ theta

include gggr roots fieldScope green principalLift clifford principalRestriction in
theorem soBrauerFieldAction_fixed (e : FieldGroup f) (Phi : SOBrauer F rootH bH) :
    letI := soBrauerFieldAction F SH literalH rootH bH hbH parameters N fieldSource C
    e • Phi = Phi :=
  soBrauerFieldTwist_fixed (literalH := literalH) gggr roots fieldScope green principalLift clifford
    principalRestriction e⁻¹ Phi

include fyz in
theorem omegaWeightFieldAction_fixed (e : FieldGroup f) (w : OmegaWeight F S b) :
    letI := omegaWeightFieldAction F S literal b hb parameters N fieldSource C
    e • w = w :=
  omegaWeightFieldTwist_fixed (rootCalibration := rootCalibration)
    (rootHCalibration := rootHCalibration) fyz e⁻¹ w

include fyz in
theorem soWeightFieldAction_fixed (e : FieldGroup f) (v : SOWeight F SH bH) :
    letI := soWeightFieldAction F SH literalH bH hbH parameters N fieldSource C
    e • v = v :=
  soWeightFieldTwist_fixed (rootCalibration := rootCalibration)
    (rootHCalibration := rootHCalibration) fyz e⁻¹ v

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
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction

include gggr fyz in
/-- Positive field equivariance of the already accepted, fixed Omega map. -/
theorem principalOmegaEquiv_fieldTwist (e : FieldGroup f) (theta : OmegaBrauer F root b) :
    omegaMap (omegaBrauerFieldTwist F S literal root b hb parameters N fieldSource C e theta) =
      omegaWeightFieldTwist F S literal b hb parameters N fieldSource C e (omegaMap theta) := by
  rw [omegaBrauerFieldTwist_fixed gggr e theta,
    omegaWeightFieldTwist_fixed (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration) fyz e (omegaMap theta)]

include gggr fyz in
/-- Positive field equivariance of that same map's accepted SO orbit descent. -/
theorem principalSOEquiv_fieldTwist (e : FieldGroup f) (Phi : SOBrauer F rootH bH) :
    soMap (soBrauerFieldTwist F SH literalH rootH bH hbH parameters N fieldSource C e Phi) =
      soWeightFieldTwist F SH literalH bH hbH parameters N fieldSource C e (soMap Phi) := by
  rw [soBrauerFieldTwist_fixed (literalH := literalH) gggr roots fieldScope green principalLift
    clifford principalRestriction e Phi,
    soWeightFieldTwist_fixed (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration) fyz e (soMap Phi)]

include gggr fyz in
/-- Left field actions use the inverse element on both exact Omega fibres. -/
theorem principalOmegaEquiv_fieldAction (e : FieldGroup f) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerFieldAction F S literal root b hb parameters N fieldSource C
    letI := omegaWeightFieldAction F S literal b hb parameters N fieldSource C
    omegaMap (e • theta) = e • omegaMap theta :=
  principalOmegaEquiv_fieldTwist (rootCalibration := rootCalibration)
    (rootHCalibration := rootHCalibration) gggr roots fieldScope green principalLift clifford
    principalRestriction fyz covering counts e⁻¹ theta

include gggr fyz in
/-- The same inverse convention applies to the exact SO descent. -/
theorem principalSOEquiv_fieldAction (e : FieldGroup f) (Phi : SOBrauer F rootH bH) :
    letI := soBrauerFieldAction F SH literalH rootH bH hbH parameters N fieldSource C
    letI := soWeightFieldAction F SH literalH bH hbH parameters N fieldSource C
    soMap (e • Phi) = e • soMap Phi :=
  principalSOEquiv_fieldTwist (literalH := literalH) (rootCalibration := rootCalibration)
    (rootHCalibration := rootHCalibration) gggr roots fieldScope green principalLift clifford
    principalRestriction fyz covering counts e⁻¹ Phi

end ModularRep.PaperProofs.TypeBRankThreePrincipalFieldMatchingSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
