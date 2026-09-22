import ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientActionBinding
import ModularRep.PaperProofs.TypeBCentralKernelSpinWeightFibreIdentification

/-!
# Specified character and weight fibres on the actual matrix Omega

The existing fibre-identification deductions are instantiated on the
constructed equivalence from the literal Spin-centre quotient to the
commutator of the actual SO carrier. Old-Omega finiteness is deduced from
that equivalence and the checked finite matrix carrier. Prescribed roots,
their full lift equality, actual block decompositions and guarded local
block/reduction packages are retained. No block matching is supplied.

The actor squares use every element of the existing residual ambient and
its actual SO/field projection. No full-automorphism identification or
Brauer-to-weight correspondence is assumed or concluded.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCliffordMatrixFibreBinding

open ModularRep TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding
open TypeBCliffordOrthogonalResidualQuotient TypeBCliffordOrthogonalAmbientActionBinding
open TypeBCentralKernelSpinFibreIdentification
open TypeBCentralKernelSpinWeightFibreIdentification
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelInertia TypeBCentralKernelLocalReduction TypeBFixedRootDefinitionFamily

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} {parameters : OddFieldParameters F r f}
  (rank : 3 ≤ n) (C : Source n F r f parameters rank N)
  (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)

include rank C centre in
/-- Finiteness comes from the constructed map into the finite matrix group. -/
theorem oldOmega_finite : Finite (TypeBSpinCoverSource.Omega N) :=
  Finite.of_injective (matrixOmegaEquiv n F N parameters rank C centre)
    (matrixOmegaEquiv n F N parameters rank C centre).injective

/- The internal implementation is parametric in a proof of finiteness.
Every public endpoint below installs the derived proof before applying it. -/
namespace Implementation

variable [Finite (TypeBSpinCoverSource.Omega N)]

local instance groupFintype (H : Type) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

section Blocks

variable {k : Type} [Field k]

/-- Actual primitive idempotents are transported by the same group-basis map. -/
def matrixPrimitiveBlockEquiv :
    LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N) ≃
      LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  primitiveBlockEquiv (matrixOmegaEquiv n F N parameters rank C centre)

@[simp] theorem matrixPrimitiveBlockEquiv_value
    (b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N)) :
    (matrixPrimitiveBlockEquiv rank C centre b).val =
      MonoidAlgebra.mapDomainRingEquiv k
        (matrixOmegaEquiv n F N parameters rank C centre) b.val := rfl

theorem matrixPrimitiveBlockEquiv_principal_iff
    (b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N)) :
    IsPrincipal (matrixPrimitiveBlockEquiv rank C centre b) ↔ IsPrincipal b :=
  primitiveBlockEquiv_principal_iff (matrixOmegaEquiv n F N parameters rank C centre) b

end Blocks

section Brauer

variable {ell : ℕ} {k K : Type}
  [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
  (oldRoot : PrimeRegularRootEmbedding ell k K (TypeBSpinCoverSource.Omega N))
  (matrixRoot : PrimeRegularRootEmbedding ell k K (TypeBOrthogonalOmegaCarriers.Omega n F))
  (lifts : matrixRoot.lift = oldRoot.lift)

/-- The target root is prescribed; the full field-level lift equality is explicit. -/
def matrixBrauerEquiv : IBr oldRoot ≃ IBr matrixRoot :=
  brauerEquiv (matrixOmegaEquiv n F N parameters rank C centre) oldRoot matrixRoot lifts

@[simp] theorem matrixBrauerEquiv_value (theta : IBr oldRoot) :
    (matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts theta).val =
      PrimeRegularClassFunction.pullback
        (matrixOmegaEquiv n F N parameters rank C centre).symm.toMonoidHom theta.val :=
  brauerEquiv_val (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts theta

theorem matrixBrauer_supported_iff
    (b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N)) (theta : IBr oldRoot) :
    Supported matrixRoot (matrixPrimitiveBlockEquiv rank C centre b)
        (matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts theta) ↔
      Supported oldRoot b theta :=
  supported_brauerEquiv_iff (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts b theta

def matrixBrauerFibreEquiv
    (b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N)) :
    BrauerFibre oldRoot b ≃
      BrauerFibre matrixRoot (matrixPrimitiveBlockEquiv rank C centre b) :=
  brauerFibreEquiv (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts b

@[simp] theorem matrixBrauerFibreEquiv_value
    (b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N))
    (theta : BrauerFibre oldRoot b) :
    (matrixBrauerFibreEquiv rank C centre oldRoot matrixRoot lifts b theta).val.val =
      PrimeRegularClassFunction.pullback
        (matrixOmegaEquiv n F N parameters rank C centre).symm.toMonoidHom theta.val.val :=
  brauerFibreEquiv_val (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts b theta

section Decompositions

variable [Fintype (LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N))]
  [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))]

/-- The selected specified block is deduced from the two literal decompositions. -/
theorem matrixBrauerBlock
    (oldBlocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N) => b.val))
    (matrixBlocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) => b.val))
    (theta : IBr oldRoot) :
    matrixPrimitiveBlockEquiv rank C centre (block oldRoot oldBlocks theta) =
      block matrixRoot matrixBlocks
        (matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts theta) :=
  selectedBlock_along (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot oldBlocks matrixBlocks theta
    (matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts theta) lifts
    (matrixBrauerEquiv_value rank C centre oldRoot matrixRoot lifts theta)

end Decompositions

variable (S : FieldActionSource n F r f parameters N)

/-- Naturality for every actual residual actor, not only the field generator. -/
theorem matrixBrauerEquiv_twist
    (a : ResidualAmbient n F parameters N S) (theta : IBr oldRoot) :
    matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts
        (IrreducibleBrauerCharacter.twist oldRoot theta
          (TypeBCentralKernelSpinBinding.omegaAction S a)) =
      IrreducibleBrauerCharacter.twist matrixRoot
        (matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts theta)
        (omegaAmbientAction S rank C
          (residualProjection n F parameters N S rank C centre a)) :=
  brauerEquiv_twist (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts (TypeBCentralKernelSpinBinding.omegaAction S a)
    (omegaAmbientAction S rank C (residualProjection n F parameters N S rank C centre a))
    (matrixOmegaEquiv_residual_action S rank C centre a) theta

theorem matrixBrauer_fixed_iff
    (a : ResidualAmbient n F parameters N S) (theta : IBr oldRoot) :
    IrreducibleBrauerCharacter.twist matrixRoot
        (matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts theta)
        (omegaAmbientAction S rank C
          (residualProjection n F parameters N S rank C centre a)) =
        matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts theta ↔
      IrreducibleBrauerCharacter.twist oldRoot theta
        (TypeBCentralKernelSpinBinding.omegaAction S a) = theta := by
  rw [← matrixBrauerEquiv_twist]
  exact (matrixBrauerEquiv rank C centre oldRoot matrixRoot lifts).injective.eq_iff

end Brauer

section OrdinaryWeights

variable {ell : ℕ} {K : Type} [Field K] [CharZero K]

def matrixRawWeightEquiv :
    CharacterWeight ell K (TypeBSpinCoverSource.Omega N) ≃
      CharacterWeight ell K (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  rawWeightEquiv (matrixOmegaEquiv n F N parameters rank C centre)

def matrixWeightClassEquiv :
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := TypeBSpinCoverSource.Omega N) ≃
      CharacterWeight.ConjugacyClass (p := ell) (K := K)
        (G := TypeBOrthogonalOmegaCarriers.Omega n F) :=
  weightClassEquiv (matrixOmegaEquiv n F N parameters rank C centre)

@[simp] theorem matrixRawWeightEquiv_subgroup
    (W : CharacterWeight ell K (TypeBSpinCoverSource.Omega N)) :
    (matrixRawWeightEquiv rank C centre W).subgroup =
      W.subgroup.map (matrixOmegaEquiv n F N parameters rank C centre).toMonoidHom := rfl

theorem matrixRawWeightEquiv_localCharacter
    (W : CharacterWeight ell K (TypeBSpinCoverSource.Omega N))
    (x : Subgroup.normalizer (W.subgroup : Set (TypeBSpinCoverSource.Omega N)))
    (y : Subgroup.normalizer ((matrixRawWeightEquiv rank C centre W).subgroup :
      Set (TypeBOrthogonalOmegaCarriers.Omega n F)))
    (hxy : matrixOmegaEquiv n F N parameters rank C centre x = y) :
    (matrixRawWeightEquiv rank C centre W).localCharacter
        (TypeBCentralKernelWeightTransport.localMk
          (matrixRawWeightEquiv rank C centre W).subgroup y) =
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup x) :=
  rawWeightEquiv_localCharacter (matrixOmegaEquiv n F N parameters rank C centre) W x y hxy

@[simp] theorem matrixWeightClassEquiv_classOf
    (W : CharacterWeight ell K (TypeBSpinCoverSource.Omega N)) :
    matrixWeightClassEquiv rank C centre (classOf W) =
      classOf (matrixRawWeightEquiv rank C centre W) := rfl

variable (S : FieldActionSource n F r f parameters N)

theorem matrixRawWeightEquiv_rightTwist
    (a : ResidualAmbient n F parameters N S)
    (W : CharacterWeight ell K (TypeBSpinCoverSource.Omega N)) :
    matrixRawWeightEquiv rank C centre
        (W.rightTwist (TypeBCentralKernelSpinBinding.omegaAction S a)) =
      (matrixRawWeightEquiv rank C centre W).rightTwist
        (omegaAmbientAction S rank C
          (residualProjection n F parameters N S rank C centre a)) :=
  rawWeightEquiv_rightTwist (matrixOmegaEquiv n F N parameters rank C centre)
    (TypeBCentralKernelSpinBinding.omegaAction S a)
    (omegaAmbientAction S rank C (residualProjection n F parameters N S rank C centre a))
    (matrixOmegaEquiv_residual_action S rank C centre a) W

theorem matrixWeightClassEquiv_rightTwist
    (a : ResidualAmbient n F parameters N S)
    (w : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := TypeBSpinCoverSource.Omega N)) :
    matrixWeightClassEquiv rank C centre
        (CharacterWeight.rightTwistConjugacyClass
          (TypeBCentralKernelSpinBinding.omegaAction S a) w) =
      CharacterWeight.rightTwistConjugacyClass
        (omegaAmbientAction S rank C
          (residualProjection n F parameters N S rank C centre a))
        (matrixWeightClassEquiv rank C centre w) :=
  weightClassEquiv_rightTwist (matrixOmegaEquiv n F N parameters rank C centre)
    (TypeBCentralKernelSpinBinding.omegaAction S a)
    (omegaAmbientAction S rank C (residualProjection n F parameters N S rank C centre a))
    (matrixOmegaEquiv_residual_action S rank C centre a) w

theorem matrixWeightClass_fixed_iff
    (a : ResidualAmbient n F parameters N S)
    (w : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := TypeBSpinCoverSource.Omega N)) :
    CharacterWeight.rightTwistConjugacyClass
        (omegaAmbientAction S rank C
          (residualProjection n F parameters N S rank C centre a))
        (matrixWeightClassEquiv rank C centre w) =
        matrixWeightClassEquiv rank C centre w ↔
      CharacterWeight.rightTwistConjugacyClass
        (TypeBCentralKernelSpinBinding.omegaAction S a) w = w := by
  rw [← matrixWeightClassEquiv_rightTwist]
  exact (matrixWeightClassEquiv rank C centre).injective.eq_iff

end OrdinaryWeights

section PhysicalWeightFibres

variable {ell : ℕ} {k K : Type}
  [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
  (oldRoot : PrimeRegularRootEmbedding ell k K (TypeBSpinCoverSource.Omega N))
  (matrixRoot : PrimeRegularRootEmbedding ell k K (TypeBOrthogonalOmegaCarriers.Omega n F))
  (lifts : matrixRoot.lift = oldRoot.lift)
  (oldBlocks : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := TypeBSpinCoverSource.Omega N)
    (Block := LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N)))
  (matrixBlocks : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F)
    (Block := LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F)))
  (oldLiteral : ∀ b, oldBlocks.operations.ambientBlockData.blockIdempotent b = b.val)
  (matrixLiteral : ∀ b, matrixBlocks.operations.ambientBlockData.blockIdempotent b = b.val)
  (reduction : Navarro318Certificate ell k K)
  (oldGuard : GuardedBlockCompatibility oldRoot oldBlocks.operations)
  (matrixGuard : GuardedBlockCompatibility matrixRoot matrixBlocks.operations)

include oldRoot matrixRoot lifts oldLiteral matrixLiteral reduction oldGuard matrixGuard in
/-- The specified weight-block equation is a reused deduction from local reductions. -/
theorem matrixWeightBlock
    (w : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := TypeBSpinCoverSource.Omega N)) :
    matrixBlocks.weightBlock (matrixWeightClassEquiv rank C centre w) =
      matrixPrimitiveBlockEquiv rank C centre (oldBlocks.weightBlock w) :=
  weightBlock_map (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts oldBlocks matrixBlocks oldLiteral matrixLiteral
    reduction oldGuard matrixGuard w

/-- Restriction of the SAME ordinary-weight class map, after its block identity. -/
def matrixWeightFibreEquiv
    (b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N)) :
    {w : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := TypeBSpinCoverSource.Omega N) // oldBlocks.weightBlock w = b} ≃
    {w : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := TypeBOrthogonalOmegaCarriers.Omega n F) //
        matrixBlocks.weightBlock w = matrixPrimitiveBlockEquiv rank C centre b} :=
  weightFibreEquiv (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts oldBlocks matrixBlocks oldLiteral matrixLiteral
    reduction oldGuard matrixGuard b

@[simp] theorem matrixWeightFibreEquiv_value
    (b : LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N))
    (w : {w : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := TypeBSpinCoverSource.Omega N) // oldBlocks.weightBlock w = b}) :
    (matrixWeightFibreEquiv rank C centre oldRoot matrixRoot lifts oldBlocks matrixBlocks
      oldLiteral matrixLiteral reduction oldGuard matrixGuard b w).val =
      matrixWeightClassEquiv rank C centre w.val := rfl

include oldRoot matrixRoot lifts oldLiteral matrixLiteral reduction oldGuard matrixGuard in
theorem matrixWeightBlock_principal_iff
    (w : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := TypeBSpinCoverSource.Omega N)) :
    IsPrincipal (matrixBlocks.weightBlock (matrixWeightClassEquiv rank C centre w)) ↔
      IsPrincipal (oldBlocks.weightBlock w) :=
  weightBlock_principal_iff (matrixOmegaEquiv n F N parameters rank C centre)
    oldRoot matrixRoot lifts oldBlocks matrixBlocks oldLiteral matrixLiteral
    reduction oldGuard matrixGuard w

end PhysicalWeightFibres

end Implementation

/- Public endpoints discharge old-Omega finiteness inside each declaration.
Their types are inferred from the actual instantiated statements, so the
same prescribed root, catalogue and local guard binders are preserved. -/

section Blocks

variable {k : Type} [Field k]

def matrixPrimitiveBlockEquiv := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixPrimitiveBlockEquiv (k := k) rank C centre

@[simp] def matrixPrimitiveBlockEquiv_value := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixPrimitiveBlockEquiv_value (k := k) rank C centre

def matrixPrimitiveBlockEquiv_principal_iff := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixPrimitiveBlockEquiv_principal_iff (k := k) rank C centre

end Blocks

section Brauer

variable {ell : ℕ} {k K : Type}
  [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]

def matrixBrauerEquiv := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauerEquiv (ell := ell) (k := k) (K := K) rank C centre

@[simp] def matrixBrauerEquiv_value := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauerEquiv_value (ell := ell) (k := k) (K := K) rank C centre

def matrixBrauer_supported_iff := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauer_supported_iff (ell := ell) (k := k) (K := K) rank C centre

def matrixBrauerFibreEquiv := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauerFibreEquiv (ell := ell) (k := k) (K := K) rank C centre

@[simp] def matrixBrauerFibreEquiv_value := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauerFibreEquiv_value (ell := ell) (k := k) (K := K) rank C centre

section Decompositions

variable [Fintype (LiteralPrimitiveBlock k (TypeBSpinCoverSource.Omega N))]
  [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))]

def matrixBrauerBlock := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauerBlock (ell := ell) (k := k) (K := K) rank C centre

end Decompositions

def matrixBrauerEquiv_twist := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauerEquiv_twist (ell := ell) (k := k) (K := K) rank C centre

def matrixBrauer_fixed_iff := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixBrauer_fixed_iff (ell := ell) (k := k) (K := K) rank C centre

end Brauer

section OrdinaryWeights

variable {ell : ℕ} {K : Type} [Field K] [CharZero K]

def matrixRawWeightEquiv := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixRawWeightEquiv (ell := ell) (K := K) rank C centre

def matrixWeightClassEquiv := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightClassEquiv (ell := ell) (K := K) rank C centre

@[simp] def matrixRawWeightEquiv_subgroup := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixRawWeightEquiv_subgroup (ell := ell) (K := K) rank C centre

def matrixRawWeightEquiv_localCharacter := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixRawWeightEquiv_localCharacter (ell := ell) (K := K) rank C centre

@[simp] def matrixWeightClassEquiv_classOf := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightClassEquiv_classOf (ell := ell) (K := K) rank C centre

def matrixRawWeightEquiv_rightTwist := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixRawWeightEquiv_rightTwist (ell := ell) (K := K) rank C centre

def matrixWeightClassEquiv_rightTwist := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightClassEquiv_rightTwist (ell := ell) (K := K) rank C centre

def matrixWeightClass_fixed_iff := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightClass_fixed_iff (ell := ell) (K := K) rank C centre

end OrdinaryWeights

section PhysicalWeightFibres

variable {ell : ℕ} {k K : Type}
  [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]

def matrixWeightBlock := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightBlock (ell := ell) (k := k) (K := K) rank C centre

def matrixWeightFibreEquiv := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightFibreEquiv (ell := ell) (k := k) (K := K) rank C centre

@[simp] def matrixWeightFibreEquiv_value := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightFibreEquiv_value (ell := ell) (k := k) (K := K) rank C centre

def matrixWeightBlock_principal_iff := by
  letI := oldOmega_finite rank C centre
  exact Implementation.matrixWeightBlock_principal_iff (ell := ell) (k := k) (K := K)
    rank C centre

end PhysicalWeightFibres

end ModularRep.PaperProofs.TypeBCliffordMatrixFibreBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
