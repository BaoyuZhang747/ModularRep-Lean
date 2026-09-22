import ModularRep.PaperProofs.TypeBSpinGGGRRationalSpanBinding
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability

/-!
# Fixation of the actual rational PIM span and its Brauer labels

These are supporting deductions for the all-rank principal selector. The
application constructs the rational GGGR basis by invoking the accepted
all-rank GGGR theorem. A basis is an internal argument here, not an external
source for that application.

The span consists of rational combinations of the original K-valued PIM
functions on the same Spin carrier. Comparing rational-linear maps on its
basis proves fixation without changing the coefficient field of the
characters or introducing a basis of the full K-span. The existing specified
PIM twist formula and column independence then fix the actual Brauer labels.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorFixedProjective

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinGGGRRationalSpanBinding
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBSpinRationalUnipotentClassBinding
open scoped MonoidAlgebra

variable {n : ℕ} {F K O k : Type}
  [Field F] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {b : LiteralPrimitiveBlock k (Spin n F N)}
  {m : ℕ}

/-- Agreement on the rational basis fixes every original K-valued function
in the actual rational PIM span. Only the scalar structure of the linear
map is restricted; the span and its vectors remain unchanged. -/
theorem projectiveQSpan_fixed_of_basis
    (B : Module.Basis (Fin m) ℚ (projectiveQSpan Msys iota b))
    (alpha : MulAut (Spin n F N))
    (basis_fixed : ∀ j, functionTwistLinearEquiv alpha (B j).val = (B j).val)
    (P : projectiveQSpan Msys iota b) :
    functionTwistLinearEquiv alpha P.val = P.val := by
  have maps_equal :
      ((functionTwistLinearEquiv (K := K) alpha).toLinearMap.restrictScalars ℚ).comp
          (projectiveQSpan Msys iota b).subtype =
        (projectiveQSpan Msys iota b).subtype := by
    apply B.ext
    intro j
    exact basis_fixed j
  exact LinearMap.congr_fun maps_equal P

/-- Every supported specified PIM belongs to this same rational span. -/
theorem projectiveIndecomposable_fixed_of_basis
    (B : Module.Basis (Fin m) ℚ (projectiveQSpan Msys iota b))
    (alpha : MulAut (Spin n F N))
    (basis_fixed : ∀ j, functionTwistLinearEquiv alpha (B j).val = (B j).val)
    (phi : IBr iota) (supported : Supported iota b phi) :
    functionTwistLinearEquiv alpha (projectiveIndecomposable Msys iota phi) =
      projectiveIndecomposable Msys iota phi :=
  projectiveQSpan_fixed_of_basis B alpha basis_fixed
    ⟨projectiveIndecomposable Msys iota phi,
      projectiveIndecomposable_mem_Q Msys iota b ⟨phi, supported⟩⟩

/-- Specified PIM equivariance and the already checked independent specified
columns transfer rational-span fixation to the original Brauer character.
Principal-block stability is derived for the very automorphism `alpha`. -/
theorem principalBrauer_fixed_of_basis
    (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (columns : DecompositionColumnIndependenceSource Msys iota)
    [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
    (blocks : BlockIdempotentDecomposition
      (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
    (principal : IsPrincipal b)
    (B : Module.Basis (Fin m) ℚ (projectiveQSpan Msys iota b))
    (alpha : MulAut (Spin n F N))
    (basis_fixed : ∀ j, functionTwistLinearEquiv alpha (B j).val = (B j).val)
    (phi : IBr iota) (supported : Supported iota b phi) :
    IrreducibleBrauerCharacter.twist iota phi alpha = phi := by
  have twisted_supported :
      Supported iota b (IrreducibleBrauerCharacter.twist iota phi alpha) :=
    TypeBCentralKernelPrincipalStability.supported_principal_twist
      blocks iota b principal alpha phi supported
  have pim_equal :
      projectiveIndecomposable Msys iota (IrreducibleBrauerCharacter.twist iota phi alpha) =
        projectiveIndecomposable Msys iota phi := by
    rw [projectiveIndecomposable_twist Msys iota hcompat alpha phi]
    exact projectiveIndecomposable_fixed_of_basis B alpha basis_fixed phi supported
  have labels_equal :
      (⟨IrreducibleBrauerCharacter.twist iota phi alpha, twisted_supported⟩ :
        {psi : IBr iota // Supported iota b psi}) = ⟨phi, supported⟩ :=
    (projectiveIndecomposable_linearIndependent
      orthogonality Msys iota columns b).injective pim_equal
  exact congrArg Subtype.val labels_equal

/-- The internal consumer of the accepted all-rank basis output and the
fixed projected GGGR family. The exhaustive class index, actual projector,
modular system, block and K-valued GGGR functions are identical on both
sides of the basis-vector equations. -/
theorem principalBrauer_fixed_of_projectedGGGRBasis
    {r : ℕ} [Finite F] [CharP F r]
    (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (columns : DecompositionColumnIndependenceSource Msys iota)
    [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
    (blocks : BlockIdempotentDecomposition
      (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
    (ordinary : OrdinaryBlockSource Msys iota blocks)
    (principal : IsPrincipal b)
    (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
    (gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K)
    (B : Module.Basis (Fin m) ℚ (projectiveQSpan Msys iota b))
    (basis_apply : ∀ j, (B j).val =
      principalProjection Msys iota b blocks ordinary (gamma (classIndex j)))
    (alpha : MulAut (Spin n F N))
    (projected_fixed : ∀ j,
      functionTwistLinearEquiv alpha
          (principalProjection Msys iota b blocks ordinary (gamma (classIndex j))) =
        principalProjection Msys iota b blocks ordinary (gamma (classIndex j)))
    (phi : IBr iota) (supported : Supported iota b phi) :
    IrreducibleBrauerCharacter.twist iota phi alpha = phi := by
  apply principalBrauer_fixed_of_basis orthogonality hcompat columns blocks principal
    B alpha ?_ phi supported
  intro j
  rw [basis_apply j]
  exact projected_fixed j

end ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorFixedProjective


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
