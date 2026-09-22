import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerFibre
import ModularRep.IrreducibleBrauerCharacterEquiv
import ModularRep.IBrBlockBasicSetBridge

/-!
# The actual automorphism action on the principal reference quotient fibre

The acting group is the original family's literal block stabilizer. Its
homomorphism on the common reference quotient is obtained through the
canonical projection equivalence. The complete inverse Brauer fibre proves
stability under those actual quotient automorphisms. The restricted action
and both equivariance equations retain the original right-action convention.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerAction

open ModularRep CharacterWeight FDRepSimpleClassKZero IBrBlockBasicSetBridge
open TypeBRankThreePrincipalCountBinding
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCentralKernelBlockSource
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open EvenFieldFLZ318FixedTheoremGate TypeBCliffordCarriers
open CyclicOuterLemma37Concrete
open TypeBRankThreePrincipalReferenceBinding TypeBRankThreePrincipalQuotientBrauerFibre

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card (G F))]
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)
  (b : LiteralPrimitiveBlock k (G F))
  {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (hb : IsPrincipal b)

/-- The same projection equivalence identifies the full actual automorphism groups. -/
def automorphismEquiv : MulAut (G F) ≃* MulAut (quotientGroup S SH literal literalH Msys root calibration navarro guard b hb) :=
  MulAut.congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)

/-- Every transported automorphism commutes with the literal quotient projection. -/
theorem automorphismEquiv_projection (alpha : MulAut (G F)) (g : G F) :
    automorphismEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb alpha (centralCharacterQuotientMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) g) = centralCharacterQuotientMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) (alpha g) := by
  have square : MulAut.congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) alpha
      (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb g) =
      quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (alpha g) := by
    change (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
      (alpha ((quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm ((quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) g))) =
    (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) (alpha g)
    rw [MulEquiv.symm_apply_apply]
  simpa only [automorphismEquiv, quotientEquiv_projection] using square

/-- The original literal stabilizer acts by its transported actual homomorphism. -/
def gammaQ : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma →* MulAut (quotientGroup S SH literal literalH Msys root calibration navarro guard b hb) :=
  (automorphismEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).toMonoidHom.comp (problem S SH literal literalH Msys root calibration navarro guard b).gamma

theorem gammaQ_projection (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (g : G F) :
    gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a (centralCharacterQuotientMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) g) = centralCharacterQuotientMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) ((problem S SH literal literalH Msys root calibration navarro guard b).gamma a g) :=
  automorphismEquiv_projection S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb ((problem S SH literal literalH Msys root calibration navarro guard b).gamma a) g

/-- The inverse in the right-action convention is retained on both sides. -/
theorem gammaQ_inverseOp (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) :
    inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a =
      MulOpposite.op ((automorphismEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) ((inverseOpHom (problem S SH literal literalH Msys root calibration navarro guard b).gamma a).unop)) := rfl

/-- Naturality holds on the complete irreducible-character sets. -/
theorem allBrauerEquiv_inverseOp
    (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (phi : IBr root) :
    allBrauerEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
      (@HSMul.hSMul (MulAut (G F))ᵐᵒᵖ (IBr root) (IBr root) inferInstance
        (inverseOpHom (problem S SH literal literalH Msys root calibration navarro guard b).gamma a) phi) =
      inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • (allBrauerEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb phi) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul
    root (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) phi (inverseOpHom (problem S SH literal literalH Msys root calibration navarro guard b).gamma a)

/-- The fixed family's action has the same quotient character values. -/
theorem fibreEquiv_inverseOp_val
    (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b)) :
    letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
    (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (a • psi)).val =
      inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).val := by
  letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
  exact allBrauerEquiv_inverseOp S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a psi.val

/-- Every element of the complete quotient fibre is stable under the actual action. -/
theorem quotientStable :
    letI := physicalBlockFintype S
    IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock.IsAutomorphismStableIBrBlock (inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))
      (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))
      (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) b := by
  letI := physicalBlockFintype S
  letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
  intro a phi membership
  let target : QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb := ⟨phi, membership⟩
  let psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b) := (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm target
  have targetValue : (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).val = phi :=
    congrArg Subtype.val ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).apply_symm_apply target)
  have actedValue : (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (a • psi)).val =
      inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • phi :=
    (fibreEquiv_inverseOp_val S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a psi).trans
      (congrArg (fun chi => inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • chi) targetValue)
  rw [← actedValue]
  exact (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (a • psi)).property

/-- The fibre action restricts actual quotient automorphisms of its Brauer characters. -/
@[instance_reducible]
def quotientAction : MulAction (problem S SH literal literalH Msys root calibration navarro guard b).Gamma (QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) := by
  letI := physicalBlockFintype S
  exact IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock.automorphismIBrBlockMulAction
    (inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) (quotientStable S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)

theorem quotientAction_val (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (phi : QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) :
    letI := quotientAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    (a • phi).val = inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • phi.val := rfl

/-- On class functions the actor is the prescribed inverse gamma value. -/
theorem quotientAction_character (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (phi : QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) :
    letI := quotientAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    (a • phi).val.val = phi.val.val.twist ((gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a⁻¹) := rfl

/-- The complete forward fibre equivalence respects the actual stabilizer action. -/
theorem fibreEquiv_equivariant
    (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b)) :
    letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
    letI := quotientAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (a • psi) = a • (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi) := by
  letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
  letI := quotientAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  apply Subtype.ext
  exact fibreEquiv_inverseOp_val S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a psi

/-- The complete reverse fibre equivalence respects that same action. -/
theorem fibreEquiv_symm_equivariant
    (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (phi : QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) :
    letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
    letI := quotientAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm (a • phi) = a • ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi) := by
  letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
  letI := quotientAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  apply (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).injective
  calc
    fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm (a • phi)) = a • phi :=
      (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).apply_symm_apply (a • phi)
    _ = a • (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi)) :=
      congrArg (fun chi => a • chi) ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).apply_symm_apply phi).symm
    _ = fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (a • ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi)) :=
      (fibreEquiv_equivariant S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi)).symm

/-- Equivariance is also an equation for the actual constructed reference descent. -/
theorem quotientBrauer_equivariant
    (a : (problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b)) :
    letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (a • psi)).brauer =
      inverseOpHom (gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer := by
  letI := definition35BrauerAction (problem S SH literal literalH Msys root calibration navarro guard b)
  exact fibreEquiv_inverseOp_val S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a psi

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
