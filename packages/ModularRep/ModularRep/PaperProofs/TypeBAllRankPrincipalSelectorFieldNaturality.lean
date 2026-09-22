import ModularRep.PaperProofs.TypeBSpinRationalUnipotentClassBinding
import ModularRep.PaperProofs.TypeBSpinPrincipalProjectiveBinding
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability

/-!
# Actual all-rank field fixation of the principal GGGR columns

The source is the existing rational-class parametrisation and Taylor
equivariance on the same norm-kernel Spin group and chosen field action.
The class and full-GGGR fixedness deductions do not require a GGGR basis
source. Principal projection is then transported by the checked specified
ordinary/decomposition-number formula and principal-block stability.

The later application uses `rational.gamma` as its literal GGGR family.
No independent family equality, selected rows, nonabelian model, D, basis,
Brauer fixedness or selector conclusion is supplied here. The algebraic
finite-point, geometric/component/Frobenius and Taylor interpretations of
the existing RationalGGGRSource remain the same explicit E1/E2/U boundary.
No rank-three application is imported as an all-rank result.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorFieldNaturality

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBRationalFieldLemma411Relative TypeBLemma411Proposition412LiteralHandoff
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding
open scoped MonoidAlgebra

variable {n r f : ℕ} {F K : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]
  {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}
  {S : FieldActionSource n F r f parameters N}
  {GeometricClass : Type}
  {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
  {geometricStable : GeometricFieldStable parameters S geometricClass}
  {ComponentGroup : GeometricClass → Type} [∀ C, Group (ComponentGroup C)]
  {inner : ∀ C, ComponentGroup C}
  (rational : RationalGGGRSource (K := K) parameters
    (Nat.le_trans (show 3 ≤ 4 by decide) rank) S
    geometricClass geometricStable ComponentGroup inner)

include rational in
/-- The accepted twisted-class calculation fixes each actual rational class.
The fibre action is the restriction of the chosen positive Spin field action. -/
theorem rationalClass_fixed (e : FieldGroup f)
    (c : UnipotentClass (r := r) (N := N)) :
    letI := unipotentClassFieldAction parameters S
    e • c = c := by
  letI := unipotentClassFieldAction parameters S
  letI : ∀ C, MulAction (FieldGroup f) (RationalFibre geometricClass C) :=
    fun C => rationalFibreFieldAction parameters S geometricClass geometricStable C
  have fixed : e • (⟨c, rfl⟩ : RationalFibre geometricClass (geometricClass c)) =
      (⟨c, rfl⟩ : RationalFibre geometricClass (geometricClass c)) :=
    (rational.parameter (geometricClass c)).smul_eq_self e ⟨c, rfl⟩
  exact congrArg Subtype.val fixed

/-- Taylor's inverse pullback convention yields fixation under the same
positive automorphism displayed in the final actual-character application. -/
theorem gamma_fixed (e : FieldGroup f)
    (c : UnipotentClass (r := r) (N := N)) :
    functionTwistLinearEquiv (K := K) (spinFieldAction n F S e) (rational.gamma c) =
      rational.gamma c := by
  letI := unipotentClassFieldAction parameters S
  letI := taylorFunctionFieldAction (K := K) (spinRightFieldHom parameters S)
  have fixed := manuscriptRightAction_gamma_eq_self rational.gamma
    rational.taylorEquivariant (rationalClass_fixed (rank := rank) rational) e c
  rw [manuscriptRightAction_eq_functionTwist (K := K)
    (spinRightFieldHom parameters S)] at fixed
  simpa only [spinRightFieldHom_unop] using fixed

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  {O k : Type} [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  (b : LiteralPrimitiveBlock k (Spin n F N)) (principal : IsPrincipal b)
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
  (ordinary : OrdinaryBlockSource Msys iota blocks)

include hcompat principal in
/-- Naturality of the literal principal Fourier projector. The principal
Brauer fibre is stable by the accepted principal-block theorem, without
assuming fixation of its individual Brauer characters. -/
theorem principalProjection_field_natural (e : FieldGroup f)
    (x : Spin n F N → K) :
    functionTwistLinearEquiv (K := K) (spinFieldAction n F S e)
        (principalProjection Msys iota b blocks ordinary x) =
      principalProjection Msys iota b blocks ordinary
        (functionTwistLinearEquiv (K := K) (spinFieldAction n F S e) x) := by
  let field := spinRightFieldHom parameters S
  have stable : ∀ (d : FieldGroup f) (phi : IBr iota), Supported iota b phi →
      Supported iota b (IrreducibleBrauerCharacter.twist iota phi (field d).unop) :=
    fun d phi supported =>
      TypeBCentralKernelPrincipalStability.supported_principal_twist
        blocks iota b principal (field d).unop phi supported
  have natural := TypeBSpinPrincipalProjectiveBinding.principalProjection_natural
    Msys iota hcompat field b stable blocks ordinary e x
  simpa only [field, spinRightFieldHom_unop] using natural.symm

include hcompat principal in
/-- Each original principal GGGR column is fixed, on the same actual norm
kernel, modular system, root, block, ordinary selector and chosen actor. -/
theorem projectedGGGR_fixed (e : FieldGroup f)
    (c : UnipotentClass (r := r) (N := N)) :
    functionTwistLinearEquiv (K := K) (spinFieldAction n F S e)
        (principalProjection Msys iota b blocks ordinary (rational.gamma c)) =
      principalProjection Msys iota b blocks ordinary (rational.gamma c) := by
  rw [principalProjection_field_natural Msys iota hcompat b principal blocks ordinary]
  rw [gamma_fixed (rank := rank) rational]

include hcompat principal in
/-- The exhaustive GGGR index is unchanged when passing fixation to the
actual rational-basis deduction. No column permutation is introduced. -/
theorem indexed_projectedGGGR_fixed {m : ℕ}
    (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
    (e : FieldGroup f) (j : Fin m) :
    functionTwistLinearEquiv (K := K) (spinFieldAction n F S e)
        (principalProjection Msys iota b blocks ordinary (rational.gamma (classIndex j))) =
      principalProjection Msys iota b blocks ordinary (rational.gamma (classIndex j)) :=
  projectedGGGR_fixed (rank := rank) rational Msys iota hcompat b principal blocks ordinary
    e (classIndex j)

end ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorFieldNaturality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
