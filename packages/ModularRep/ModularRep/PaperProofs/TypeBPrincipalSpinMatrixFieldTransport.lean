import ModularRep.PaperProofs.TypeBCliffordMatrixFibreBinding
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability

/-!
# Principal Brauer field fixation from literal Spin to matrix Omega

The route is the literal quotient of Spin by its centre, followed by the
already constructed matrixOmegaEquiv. Only finite Spin is required; no
finite Clifford semidirect ambient is introduced. Central inflation,
specified block transport and actual field squares are reused.

Spin fixation is a transport premise here, to be discharged by the indexed
GGGR deduction in a later application. It is not an external source field.
The target principal block is identified by its specified decomposition,
and prescribed root lift functions remain explicit.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalSpinMatrixFieldTransport

open ModularRep TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCliffordOrthogonalSourceBinding TypeBCliffordOrthogonalFullFieldBinding
open TypeBCliffordMatrixFibreBinding

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} [Finite (Spin n F N)]

/-- The literal centre has order two by the retained scoped centre source. -/
theorem centre_isTwoGroup (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N) :
    IsPGroup 2 (Subgroup.center (Spin n F N)) := by
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using centre.centre_order parameters rank

variable (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
  (C : Source n F r f parameters rank N)
  (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (oldRoot : PrimeRegularRootEmbedding 2 k K (TypeBSpinCoverSource.Omega N))
  (matrixRoot : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega n F))
  (matrixLifts : matrixRoot.lift = oldRoot.lift)

/-- Canonical Spin roots induced by the same prescribed Spin-centre quotient root. -/
abbrev canonicalSpinRoot : PrimeRegularRootEmbedding 2 k K (Spin n F N) :=
  TypeBCentralKernelBrauerInflation.upRoot (Subgroup.center (Spin n F N))
    (centre_isTwoGroup parameters rank centre) oldRoot

theorem canonicalSpinRoot_lift :
    (canonicalSpinRoot parameters rank centre oldRoot).lift = oldRoot.lift := by
  funext z
  exact PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
    (Subgroup.center (Spin n F N)) (centre_isTwoGroup parameters rank centre) oldRoot z

/-- A prescribed source root is identified by its actual full lift, not its name. -/
theorem spinRoot_eq_canonical
    (spinRoot : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (spinLifts : spinRoot.lift = oldRoot.lift) :
    spinRoot = canonicalSpinRoot parameters rank centre oldRoot :=
  TypeBCentralKernelSpinFibreIdentification.root_eq_of_lift_eq _ _
    (spinLifts.trans (canonicalSpinRoot_lift parameters rank centre oldRoot).symm)

variable (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k)
  (regular : TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{0} 2)
  (blocks : NavarroCentralBlockPrinciple 2 k)

/-- The actual quotient algebra map followed by the fixed matrix group algebra map. -/
def spinMatrixBlockEquiv :
    LiteralPrimitiveBlock k (Spin n F N) ≃
      LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  (blockEquiv (Subgroup.center (Spin n F N))
    (centre_isTwoGroup parameters rank centre) le_rfl oldRoot blocks).trans
    (matrixPrimitiveBlockEquiv rank C centre)

theorem spinMatrixBlockEquiv_principal_iff (b : LiteralPrimitiveBlock k (Spin n F N)) :
    IsPrincipal (spinMatrixBlockEquiv parameters rank C centre oldRoot blocks b) ↔
      IsPrincipal b :=
  (matrixPrimitiveBlockEquiv_principal_iff rank C centre _).trans
    (blockEquiv_principal_iff (Subgroup.center (Spin n F N))
      (centre_isTwoGroup parameters rank centre) le_rfl oldRoot blocks b)

/-- Character descent and the existing matrix isomorphism use the same quotient root. -/
def spinMatrixBrauerEquiv :
    IBr (canonicalSpinRoot parameters rank centre oldRoot) ≃ IBr matrixRoot :=
  (TypeBCentralKernelBrauerInflation.brauerEquiv (Subgroup.center (Spin n F N))
    (centre_isTwoGroup parameters rank centre) oldRoot kernel regular).symm.trans
    (matrixBrauerEquiv rank C centre oldRoot matrixRoot matrixLifts)

/-- The fibre map is restricted only after both specified support compatibilities. -/
def spinMatrixBrauerFibreEquiv (b : LiteralPrimitiveBlock k (Spin n F N)) :
    BrauerFibre (canonicalSpinRoot parameters rank centre oldRoot) b ≃
      BrauerFibre matrixRoot (spinMatrixBlockEquiv parameters rank C centre oldRoot blocks b) :=
  (brauerBlockEquiv (Subgroup.center (Spin n F N))
    (centre_isTwoGroup parameters rank centre) le_rfl oldRoot kernel regular blocks b).symm.trans
    (matrixBrauerFibreEquiv rank C centre oldRoot matrixRoot matrixLifts
      (blockEquiv (Subgroup.center (Spin n F N))
        (centre_isTwoGroup parameters rank centre) le_rfl oldRoot blocks b))

theorem spinMatrixBrauerFibreEquiv_val (b : LiteralPrimitiveBlock k (Spin n F N))
    (theta : BrauerFibre (canonicalSpinRoot parameters rank centre oldRoot) b) :
    (spinMatrixBrauerFibreEquiv parameters rank C centre oldRoot matrixRoot matrixLifts
      kernel regular blocks b theta).val =
        spinMatrixBrauerEquiv parameters rank C centre oldRoot matrixRoot matrixLifts
          kernel regular theta.val := rfl

variable (S : FieldActionSource n F r f parameters N)

/-- The old quotient field action is the existing literal residual action
at the image of the same actual field element. -/
def spinQuotientFieldAction : FieldGroup f →* MulAut (TypeBSpinCoverSource.Omega N) :=
  (TypeBCentralKernelSpinBinding.omegaAction S).comp
    ((TypeBCentralKernelCarriers.qA (TypeBCentralKernelSpinBinding.P S)).comp
      SemidirectProduct.inr)

theorem spinQuotientFieldAction_mk (e : FieldGroup f) (g : Spin n F N) :
    spinQuotientFieldAction parameters S e
      (QuotientGroup.mk' (Subgroup.center (Spin n F N)) g) =
        QuotientGroup.mk' (Subgroup.center (Spin n F N)) (spinFieldAction n F S e g) := by
  change TypeBCentralKernelSpinBinding.omegaAction S
    (TypeBCentralKernelCarriers.qA (TypeBCentralKernelSpinBinding.P S)
      (SemidirectProduct.inr e)) _ = _
  rw [TypeBCentralKernelSpinBinding.omegaAction_mk,
    TypeBAutomorphismSource.ambientAutomorphism_inr]

/-- Actual all-field naturality of the full Spin-to-matrix Brauer map. -/
theorem spinMatrixBrauerEquiv_twist (e : FieldGroup f)
    (theta : IBr (canonicalSpinRoot parameters rank centre oldRoot)) :
    spinMatrixBrauerEquiv parameters rank C centre oldRoot matrixRoot matrixLifts kernel regular
      (IrreducibleBrauerCharacter.twist _ theta (spinFieldAction n F S e)) =
        IrreducibleBrauerCharacter.twist matrixRoot
          (spinMatrixBrauerEquiv parameters rank C centre oldRoot matrixRoot matrixLifts
            kernel regular theta) (omegaFieldAction S rank C e) := by
  obtain ⟨phi, rfl⟩ :=
    (TypeBCentralKernelBrauerInflation.brauerEquiv (Subgroup.center (Spin n F N))
      (centre_isTwoGroup parameters rank centre) oldRoot kernel regular).surjective theta
  have inflation := TypeBCentralKernelBrauerInflation.brauerEquiv_twist
    (Subgroup.center (Spin n F N)) (centre_isTwoGroup parameters rank centre) oldRoot
    kernel regular (spinFieldAction n F S e) (spinQuotientFieldAction parameters S e)
    (fun g => (spinQuotientFieldAction_mk parameters S e g).symm) phi
  change matrixBrauerEquiv rank C centre oldRoot matrixRoot matrixLifts
    ((TypeBCentralKernelBrauerInflation.brauerEquiv (Subgroup.center (Spin n F N))
      (centre_isTwoGroup parameters rank centre) oldRoot kernel regular).symm _) =
    IrreducibleBrauerCharacter.twist matrixRoot
      (matrixBrauerEquiv rank C centre oldRoot matrixRoot matrixLifts
        ((TypeBCentralKernelBrauerInflation.brauerEquiv (Subgroup.center (Spin n F N))
          (centre_isTwoGroup parameters rank centre) oldRoot kernel regular).symm
          (TypeBCentralKernelBrauerInflation.brauerEquiv (Subgroup.center (Spin n F N))
            (centre_isTwoGroup parameters rank centre) oldRoot kernel regular phi)))
      (omegaFieldAction S rank C e)
  rw [← inflation, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change matrixBrauerEquiv rank C centre oldRoot matrixRoot matrixLifts
      (IrreducibleBrauerCharacter.twist oldRoot phi (spinQuotientFieldAction parameters S e)) =
    IrreducibleBrauerCharacter.twist matrixRoot
      (matrixBrauerEquiv rank C centre oldRoot matrixRoot matrixLifts phi)
      (omegaFieldAction S rank C e)
  exact TypeBCentralKernelSpinFibreIdentification.brauerEquiv_twist
    (matrixOmegaEquiv n F N parameters rank C centre) oldRoot matrixRoot matrixLifts
    (spinQuotientFieldAction parameters S e) (omegaFieldAction S rank C e)
    (matrixOmegaEquiv_field_action S rank C centre e) phi

variable [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))]
  (matrixBlocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) => b.val))

include matrixBlocks in
/-- The prescribed principal matrix block is the computed image of the
actual principal Spin block, by specified principal uniqueness. -/
theorem spinMatrixBlock_eq_principal
    (spinBlock : LiteralPrimitiveBlock k (Spin n F N)) (spinPrincipal : IsPrincipal spinBlock)
    (matrixBlock : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))
    (matrixPrincipal : IsPrincipal matrixBlock) :
    spinMatrixBlockEquiv parameters rank C centre oldRoot blocks spinBlock = matrixBlock :=
  TypeBCentralKernelPrincipalStability.principal_unique matrixBlocks _ matrixBlock
    ((spinMatrixBlockEquiv_principal_iff parameters rank C centre oldRoot blocks spinBlock).mpr
      spinPrincipal) matrixPrincipal

include matrixLifts kernel regular blocks matrixBlocks centre in
/-- Canonical-root transport: the Spin fixation premise is used only here
as an input to transport, not stored in any external source record. -/
theorem matrix_fixed_of_canonicalSpin_fixed
    (spinBlock : LiteralPrimitiveBlock k (Spin n F N)) (spinPrincipal : IsPrincipal spinBlock)
    (matrixBlock : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))
    (matrixPrincipal : IsPrincipal matrixBlock)
    (spinFixed : ∀ (e : FieldGroup f) (theta : IBr (canonicalSpinRoot parameters rank centre oldRoot)),
      Supported (canonicalSpinRoot parameters rank centre oldRoot) spinBlock theta →
        IrreducibleBrauerCharacter.twist _ theta (spinFieldAction n F S e) = theta) :
    ∀ (e : FieldGroup f) (phi : IBr matrixRoot),
      Supported matrixRoot matrixBlock phi →
        IrreducibleBrauerCharacter.twist matrixRoot phi (omegaFieldAction S rank C e) = phi := by
  intro e phi supported
  have blockEqual := spinMatrixBlock_eq_principal parameters rank C centre oldRoot blocks
    matrixBlocks spinBlock spinPrincipal matrixBlock matrixPrincipal
  let target : BrauerFibre matrixRoot
      (spinMatrixBlockEquiv parameters rank C centre oldRoot blocks spinBlock) :=
    ⟨phi, blockEqual.symm ▸ supported⟩
  obtain ⟨theta, htheta⟩ :=
    (spinMatrixBrauerFibreEquiv parameters rank C centre oldRoot matrixRoot matrixLifts
      kernel regular blocks spinBlock).surjective target
  have values :
      spinMatrixBrauerEquiv parameters rank C centre oldRoot matrixRoot matrixLifts
        kernel regular theta.val = phi := congrArg Subtype.val htheta
  calc
    IrreducibleBrauerCharacter.twist matrixRoot phi (omegaFieldAction S rank C e) =
        IrreducibleBrauerCharacter.twist matrixRoot
          (spinMatrixBrauerEquiv parameters rank C centre oldRoot matrixRoot matrixLifts
            kernel regular theta.val) (omegaFieldAction S rank C e) := by rw [values]
    _ = spinMatrixBrauerEquiv parameters rank C centre oldRoot matrixRoot matrixLifts kernel regular
        (IrreducibleBrauerCharacter.twist _ theta.val (spinFieldAction n F S e)) :=
      (spinMatrixBrauerEquiv_twist parameters rank C centre oldRoot matrixRoot matrixLifts
        kernel regular S e theta.val).symm
    _ = spinMatrixBrauerEquiv parameters rank C centre oldRoot matrixRoot matrixLifts kernel regular
        theta.val := congrArg _ (spinFixed e theta.val theta.property)
    _ = phi := values

include matrixLifts kernel regular blocks matrixBlocks centre in
/-- Prescribed-root endpoint. Full lift equality identifies the actual
Spin root with the canonical inflation root before transporting fixation. -/
theorem matrix_fixed_of_spin_fixed
    (spinRoot : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (spinLifts : spinRoot.lift = oldRoot.lift)
    (spinBlock : LiteralPrimitiveBlock k (Spin n F N)) (spinPrincipal : IsPrincipal spinBlock)
    (matrixBlock : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))
    (matrixPrincipal : IsPrincipal matrixBlock)
    (spinFixed : ∀ (e : FieldGroup f) (theta : IBr spinRoot),
      Supported spinRoot spinBlock theta →
        IrreducibleBrauerCharacter.twist spinRoot theta (spinFieldAction n F S e) = theta) :
    ∀ (e : FieldGroup f) (phi : IBr matrixRoot),
      Supported matrixRoot matrixBlock phi →
        IrreducibleBrauerCharacter.twist matrixRoot phi (omegaFieldAction S rank C e) = phi := by
  have rootEqual := spinRoot_eq_canonical parameters rank centre oldRoot spinRoot spinLifts
  subst spinRoot
  exact matrix_fixed_of_canonicalSpin_fixed parameters rank C centre oldRoot matrixRoot matrixLifts
    kernel regular blocks S matrixBlocks spinBlock spinPrincipal matrixBlock matrixPrincipal spinFixed

end ModularRep.PaperProofs.TypeBPrincipalSpinMatrixFieldTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
