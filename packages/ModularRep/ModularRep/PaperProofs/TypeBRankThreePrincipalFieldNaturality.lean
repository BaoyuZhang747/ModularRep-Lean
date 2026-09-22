import ModularRep.PaperProofs.TypeBRankThreePrincipalBrauerOrbitBinding
import ModularRep.PaperProofs.TypeBCliffordOrthogonalFullFieldBinding
import ModularRep.CyclicOuterBrauerExtension

/-!
# Field naturality on the four literal rank-three principal fibres

Principal-block stability restricts the actual automorphisms to Brauer
characters and ordinary weight classes. Green uniqueness and the checked
restriction-occurrence square prove naturality of the SAME principal SO
character above an Omega constituent. No character or weight fixedness,
correspondence equivariance, or DGN covariance is a source input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalFieldNaturality

open ModularRep CharacterWeight
open TypeBCentralKernelCarriers TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelPrincipalStability TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalBrauerOrbitBinding TypeBGreenPrincipalConstituentSource
open NavarroCoveringBrauerExtension
open TypeBCliffordCarriers TypeBCliffordOrthogonalAmbientQuotient
open TypeBCliffordOrthogonalFullFieldBinding CyclicOuterLemma37Concrete

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section RestrictedActions

variable {k K X : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (S : LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X) (Block := LiteralPrimitiveBlock k X))
    (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)

/-- The specified decomposition used by this very weight assignment. -/
def physicalDecomposition :
    letI := S.operations.ambientBlockData.fintypeBlock
    BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k X => b.val) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  have values : S.operations.ambientBlockData.blockIdempotent =
      (fun b : LiteralPrimitiveBlock k X => b.val) := funext literal
  rw [← values]
  exact S.operations.ambientBlockData.blocks

variable (root : PrimeRegularRootEmbedding 2 k K X)
    (b : LiteralPrimitiveBlock k X) (hb : IsPrincipal b)

/-- All actual opposite automorphisms preserve this principal weight fibre. -/
def principalWeightOpAction : MulAction (MulAut X)ᵐᵒᵖ (S.Fibre b) where
  smul alpha w := ⟨alpha • w.val, by
    letI := S.operations.ambientBlockData.fintypeBlock
    change S.weightBlock (alpha • w.val) = b
    have hw : S.weightBlock w.val = b := w.property
    exact (S.weightBlock_transport alpha w.val).trans
      ((congrArg (fun c : LiteralPrimitiveBlock k X => alpha • c) hw).trans
        (principal_op_smul_eq (physicalDecomposition S literal) b hb alpha))⟩
  one_smul w := Subtype.ext (one_smul (MulAut X)ᵐᵒᵖ w.val)
  mul_smul alpha beta w := Subtype.ext (mul_smul alpha beta w.val)

/-- The restricted positive right twist is a permutation of the SAME
supported principal Brauer fibre. -/
def brauerTwistEquiv (alpha : MulAut X) : BrauerFibre root b ≃ BrauerFibre root b := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := principalFibreMulAction (physicalDecomposition S literal) root b hb
  exact MulAction.toPerm (MulOpposite.op alpha)

@[simp] theorem brauerTwistEquiv_val (alpha : MulAut X) (theta : BrauerFibre root b) :
    (brauerTwistEquiv S literal root b hb alpha theta).val =
      IrreducibleBrauerCharacter.twist root theta.val alpha := rfl

/-- The restricted positive right twist on the SAME ordinary weight-class fibre. -/
def weightTwistEquiv (alpha : MulAut X) : S.Fibre b ≃ S.Fibre b := by
  letI := principalWeightOpAction S literal b hb
  exact MulAction.toPerm (MulOpposite.op alpha)

@[simp] theorem weightTwistEquiv_val (alpha : MulAut X) (w : S.Fibre b) :
    (weightTwistEquiv S literal b hb alpha w).val =
      CharacterWeight.rightTwistConjugacyClass alpha w.val := rfl

variable {E : Type} [Group E] (rho : E →* MulAut X)

/-- Left action encoding the right automorphism action, hence rho(e inverse). -/
def brauerFieldAction : MulAction E (BrauerFibre root b) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := principalFibreMulAction (physicalDecomposition S literal) root b hb
  exact rightAutomorphismAction rho

def weightFieldAction : MulAction E (S.Fibre b) := by
  letI := principalWeightOpAction S literal b hb
  exact rightAutomorphismAction rho

@[simp] theorem brauerFieldAction_val (e : E) (theta : BrauerFibre root b) :
    letI := brauerFieldAction S literal root b hb rho
    (e • theta).val = IrreducibleBrauerCharacter.twist root theta.val (rho e⁻¹) := rfl

@[simp] theorem weightFieldAction_val (e : E) (w : S.Fibre b) :
    letI := weightFieldAction S literal b hb rho
    (e • w).val = CharacterWeight.rightTwistConjugacyClass (rho e⁻¹) w.val := rfl

end RestrictedActions

section ActualRankThree

variable (F : Type) [Field F] [Finite F]
    {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
    (S : OmegaWeightSource (k := k) (K := K) F)
    (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
    (root : PrimeRegularRootEmbedding 2 k K (G F))
    (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
    (SH : SOWeightSource (k := k) (K := K) F)
    (literalH : ∀ b, SH.operations.ambientBlockData.blockIdempotent b = b.val)
    (rootH : PrimeRegularRootEmbedding 2 k K (H F))
    (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
    {r f : ℕ} [CharP F r]
    (parameters : OddFieldParameters F r f)
    (N : NormSource 3 F)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (C : TypeBCliffordOrthogonalSourceBinding.Source
      3 F r f parameters (Nat.le_refl 3) N)

def omegaBrauerFieldTwist (e : FieldGroup f) :
    OmegaBrauer F root b ≃ OmegaBrauer F root b :=
  brauerTwistEquiv S literal root b hb
    (omegaFieldAction fieldSource (Nat.le_refl 3) C e)

def soBrauerFieldTwist (e : FieldGroup f) :
    SOBrauer F rootH bH ≃ SOBrauer F rootH bH :=
  brauerTwistEquiv SH literalH rootH bH hbH
    (soFieldAction 3 F parameters (Nat.le_refl 3) N C fieldSource e)

def omegaWeightFieldTwist (e : FieldGroup f) :
    OmegaWeight F S b ≃ OmegaWeight F S b :=
  weightTwistEquiv S literal b hb
    (omegaFieldAction fieldSource (Nat.le_refl 3) C e)

def soWeightFieldTwist (e : FieldGroup f) :
    SOWeight F SH bH ≃ SOWeight F SH bH :=
  weightTwistEquiv SH literalH bH hbH
    (soFieldAction 3 F parameters (Nat.le_refl 3) N C fieldSource e)

def omegaBrauerFieldAction : MulAction (FieldGroup f) (OmegaBrauer F root b) :=
  brauerFieldAction S literal root b hb (omegaFieldAction fieldSource (Nat.le_refl 3) C)

def soBrauerFieldAction : MulAction (FieldGroup f) (SOBrauer F rootH bH) :=
  brauerFieldAction SH literalH rootH bH hbH
    (soFieldAction 3 F parameters (Nat.le_refl 3) N C fieldSource)

def omegaWeightFieldAction : MulAction (FieldGroup f) (OmegaWeight F S b) :=
  weightFieldAction S literal b hb (omegaFieldAction fieldSource (Nat.le_refl 3) C)

def soWeightFieldAction : MulAction (FieldGroup f) (SOWeight F SH bH) :=
  weightFieldAction SH literalH bH hbH
    (soFieldAction 3 F parameters (Nat.le_refl 3) N C fieldSource)

@[simp] theorem omegaBrauerFieldAction_eq_twist (e : FieldGroup f)
    (theta : OmegaBrauer F root b) :
    letI := omegaBrauerFieldAction F S literal root b hb parameters N fieldSource C
    e • theta = omegaBrauerFieldTwist F S literal root b hb parameters N fieldSource C e⁻¹ theta :=
  rfl

@[simp] theorem soBrauerFieldAction_eq_twist (e : FieldGroup f)
    (Phi : SOBrauer F rootH bH) :
    letI := soBrauerFieldAction F SH literalH rootH bH hbH parameters N fieldSource C
    e • Phi = soBrauerFieldTwist F SH literalH rootH bH hbH parameters N fieldSource C e⁻¹ Phi :=
  rfl

@[simp] theorem omegaWeightFieldAction_eq_twist (e : FieldGroup f)
    (w : OmegaWeight F S b) :
    letI := omegaWeightFieldAction F S literal b hb parameters N fieldSource C
    e • w = omegaWeightFieldTwist F S literal b hb parameters N fieldSource C e⁻¹ w := rfl

@[simp] theorem soWeightFieldAction_eq_twist (e : FieldGroup f)
    (v : SOWeight F SH bH) :
    letI := soWeightFieldAction F SH literalH bH hbH parameters N fieldSource C
    e • v = soWeightFieldTwist F SH literalH bH hbH parameters N fieldSource C e⁻¹ v := rfl

variable (roots : RootAgreement (G F) rootH root)
    (fieldScope : SpathCoefficientField 2 k rootH.prime)
    (indexTwo : (G F).index = 2)
    (green : Green811Source (G F) rootH root roots fieldScope
      (quotient_isTwoGroup (G F) indexTwo))
    (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
      (quotient_isTwoGroup (G F) indexTwo))

/-- The already selected SO character above a constituent commutes with
the actual field twist. The source is Green uniqueness; the occurrence
transport is the existing checked literal inclusion square. -/
theorem principalAbove_fieldTwist (e : FieldGroup f) (theta : OmegaBrauer F root b) :
    principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift
      (omegaBrauerFieldTwist F S literal root b hb parameters N fieldSource C e theta) =
    soBrauerFieldTwist F SH literalH rootH bH hbH parameters N fieldSource C e
      (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift
        theta) := by
  apply principalAbove_eq F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift
  exact TypeBCharacteristicTwoConstituentSource.occursInRestriction_twist (G F) rootH root
    (soFieldAction 3 F parameters (Nat.le_refl 3) N C fieldSource e)
    (omegaFieldAction fieldSource (Nat.le_refl 3) C e)
    (fun _ => rfl)
    (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift
      theta).val theta.val
    (principalAbove_occurs F root b hb rootH bH hbH roots fieldScope indexTwo green
      principalLift theta)

/-- The same equality in the inverse-actor left action convention. -/
theorem principalAbove_fieldAction (e : FieldGroup f) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerFieldAction F S literal root b hb parameters N fieldSource C
    letI := soBrauerFieldAction F SH literalH rootH bH hbH parameters N fieldSource C
    principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift
      (e • theta) =
      e • principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo green principalLift
        theta :=
  principalAbove_fieldTwist F S literal root b hb SH literalH rootH bH hbH
    parameters N fieldSource C roots fieldScope indexTwo green principalLift e⁻¹ theta

end ActualRankThree

end ModularRep.PaperProofs.TypeBRankThreePrincipalFieldNaturality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
