import ModularRep.PaperProofs.TypeBCentralKernelWeightBlockTransport
import ModularRep.PaperProofs.TypeBCentralKernelInertia
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability

/-!
# Construction of the actual block-fibre bijection across a central p-kernel

The input bijection is on the quotient's actual supported Brauer fibre and
actual weight fibre. Inflation and weight descent have already been proved.
Their composition constructs the upstairs bijection; no upstairs bijection
or inductive-condition predicate is an external input. Naturality is proved
for each specified pair of automorphisms and hence for the actual A/P actor.

The specified normalizer compatibility in `TransportData` is intermediate
data, to be supplied by the guarded local-block binding. It is not declared
to be a literature certificate here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelFibreAssembly

open TypeBCentralKernelBrauerInflation TypeBCentralKernelBlockSource
open TypeBCentralKernelWeightTransport TypeBCentralKernelWeightBlockTransport
open TypeBCentralKernelCarriers

universe u

local instance finiteGroupFintype (X : Type u) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {p : ℕ} {k K H : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group H] [Finite H]

structure TransportData (P : Subgroup H) [P.Normal] (hP : IsPGroup p P)
    (central : P ≤ Subgroup.center H)
    (iotaDown : PrimeRegularRootEmbedding p k K (H ⧸ P)) where
  kernel : Navarro232Principle p k
  regular : PrimeRegularQuotientLiftPrinciple.{u} p
  blocks : NavarroCentralBlockPrinciple p k
  up : CharacterWeight.LocalBlockInductionSource
    (p := p) (k := k) (K := K) (G := H) (Block := LiteralPrimitiveBlock k H)
  down : CharacterWeight.LocalBlockInductionSource
    (p := p) (k := k) (K := K) (G := H ⧸ P)
    (Block := LiteralPrimitiveBlock k (H ⧸ P))
  upLiteral : ∀ b, up.operations.ambientBlockData.blockIdempotent b = b.val
  downLiteral : ∀ b, down.operations.ambientBlockData.blockIdempotent b = b.val
  localPhysical : LocalNormalizerCompatibility P hP up.operations down.operations

variable {P : Subgroup H} [P.Normal] {hP : IsPGroup p P}
  {central : P ≤ Subgroup.center H}
  {iotaDown : PrimeRegularRootEmbedding p k K (H ⧸ P)}
  (D : TransportData P hP central iotaDown) (b : LiteralPrimitiveBlock k H)

abbrev DownBrauer := {phi : IBr iotaDown // Supported iotaDown
  (blockEquiv P hP central iotaDown D.blocks b) phi}

abbrev UpBrauer (_D : TransportData P hP central iotaDown) (b : LiteralPrimitiveBlock k H) :=
  {phi : IBr (upRoot P hP iotaDown) //
  Supported (upRoot P hP iotaDown) b phi}

abbrev DownWeight := {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H ⧸ P) //
  D.down.weightBlock w = blockEquiv P hP central iotaDown D.blocks b}

abbrev UpWeight := {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H) //
  D.up.weightBlock w = b}

def brauerLift : DownBrauer D b ≃ UpBrauer D b :=
  brauerBlockEquiv P hP central iotaDown D.kernel D.regular D.blocks b

def weightDescend : UpWeight D b ≃ DownWeight D b :=
  weightBlockEquiv P hP central iotaDown D.blocks D.up D.down
    D.upLiteral D.downLiteral D.localPhysical b

/-- The only supplied bijection is the quotient hypothesis on literal fibres. -/
def liftedBijection (omegaDown : DownBrauer D b ≃ DownWeight D b) :
    UpBrauer D b ≃ UpWeight D b :=
  (brauerLift D b).symm.trans (omegaDown.trans (weightDescend D b).symm)

theorem brauerLift_value (phi : DownBrauer D b) :
    (brauerLift D b phi).val = brauerEquiv P hP iotaDown D.kernel D.regular phi.val := rfl

theorem weightDescend_value (w : UpWeight D b) :
    (weightDescend D b w).val = quotientConjugacyClassEquiv (K := K) P hP w.val := rfl

def liftedMap (omegaDown : DownBrauer D b ≃ DownWeight D b) :
    UpBrauer D b → CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H) :=
  fun theta => (liftedBijection D b omegaDown theta).val

theorem liftedMap_injective (omegaDown : DownBrauer D b ≃ DownWeight D b) :
    Function.Injective (liftedMap D b omegaDown) := by
  intro theta theta' h
  exact (liftedBijection D b omegaDown).injective (Subtype.ext h)

/-- The supplied ambient allocation is rewritten to the literal idempotent
value before the principal-block stability theorem is used. -/
def upDecomposition :
    letI := D.up.operations.ambientBlockData.fintypeBlock
    BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k H => b.val) := by
  letI := D.up.operations.ambientBlockData.fintypeBlock
  have allocation : D.up.operations.ambientBlockData.blockIdempotent =
      (fun b : LiteralPrimitiveBlock k H => b.val) := funext D.upLiteral
  rw [← allocation]
  exact D.up.operations.ambientBlockData.blocks

theorem principal_supported_twist (hb : IsPrincipal b) (alpha : MulAut H)
    (theta : UpBrauer D b) : Supported (upRoot P hP iotaDown) b
      (IrreducibleBrauerCharacter.twist (upRoot P hP iotaDown) theta.val alpha) := by
  letI := D.up.operations.ambientBlockData.fintypeBlock
  exact TypeBCentralKernelPrincipalStability.supported_principal_twist
    (upDecomposition D) (upRoot P hP iotaDown) b hb alpha theta.val theta.property

theorem descended_liftedBijection (omegaDown : DownBrauer D b ≃ DownWeight D b)
    (theta : UpBrauer D b) :
    quotientConjugacyClassEquiv (K := K) P hP (liftedBijection D b omegaDown theta).val =
      (omegaDown ((brauerLift D b).symm theta)).val := by
  exact congrArg Subtype.val ((weightDescend D b).apply_symm_apply _)

theorem descendedBrauer_twist (alpha : MulAut H) (beta : MulAut (H ⧸ P))
    (square : ∀ g, QuotientGroup.mk' P (alpha g) = beta (QuotientGroup.mk' P g))
    (theta theta' : UpBrauer D b)
    (hTheta : theta'.val = IrreducibleBrauerCharacter.twist (upRoot P hP iotaDown)
      theta.val alpha) :
    ((brauerLift D b).symm theta').val = IrreducibleBrauerCharacter.twist iotaDown
      ((brauerLift D b).symm theta).val beta := by
  apply (brauerEquiv P hP iotaDown D.kernel D.regular).injective
  rw [brauerEquiv_twist P hP iotaDown D.kernel D.regular alpha beta square]
  have ht := congrArg Subtype.val ((brauerLift D b).apply_symm_apply theta)
  have ht' := congrArg Subtype.val ((brauerLift D b).apply_symm_apply theta')
  change brauerEquiv P hP iotaDown D.kernel D.regular
    ((brauerLift D b).symm theta).val = theta.val at ht
  change brauerEquiv P hP iotaDown D.kernel D.regular
    ((brauerLift D b).symm theta').val = theta'.val at ht'
  rw [ht, ht', hTheta]

/-- Pointwise naturality on the actual fibre carriers. No action of the full
automorphism group is required of the quotient hypothesis. -/
theorem liftedBijection_twist (omegaDown : DownBrauer D b ≃ DownWeight D b)
    (alpha : MulAut H) (beta : MulAut (H ⧸ P))
    (square : ∀ g, QuotientGroup.mk' P (alpha g) = beta (QuotientGroup.mk' P g))
    (equivariantDown : ∀ phi phi' : DownBrauer D b,
      phi'.val = IrreducibleBrauerCharacter.twist iotaDown phi.val beta →
      (omegaDown phi').val = CharacterWeight.rightTwistConjugacyClass beta
        (omegaDown phi).val)
    (theta theta' : UpBrauer D b)
    (hTheta : theta'.val = IrreducibleBrauerCharacter.twist (upRoot P hP iotaDown)
      theta.val alpha) :
    (liftedBijection D b omegaDown theta').val =
      CharacterWeight.rightTwistConjugacyClass alpha (liftedBijection D b omegaDown theta).val := by
  apply (quotientConjugacyClassEquiv (K := K) P hP).injective
  rw [descended_liftedBijection D b omegaDown theta']
  have natural := conjugacyClassEquiv_rightTwist (p := p) (K := K)
    (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
    (by rw [QuotientGroup.ker_mk']; exact hP) alpha beta square
    (liftedBijection D b omegaDown theta).val
  change quotientConjugacyClassEquiv (K := K) P hP
    (CharacterWeight.rightTwistConjugacyClass alpha (liftedBijection D b omegaDown theta).val) =
    CharacterWeight.rightTwistConjugacyClass beta
      (quotientConjugacyClassEquiv (K := K) P hP (liftedBijection D b omegaDown theta).val) at natural
  rw [natural, descended_liftedBijection D b omegaDown theta]
  exact equivariantDown _ _ (descendedBrauer_twist D b alpha beta square theta theta' hTheta)

section Ambient

variable {A : Type u} [Group A] [Finite A]
  (G Z : Subgroup A) [G.Normal] [Z.Normal]
  (hZG : Z ≤ G) (hZ : IsPGroup p (kernelInG G Z))
  (hcentral : kernelInG G Z ≤ Subgroup.center G)
  (root : PrimeRegularRootEmbedding p k K (QuotientG G Z))
  (data : TransportData (kernelInG G Z) hZ hcentral root)
  (B : LiteralPrimitiveBlock k G)
  (omegaDown : DownBrauer data B ≃ DownWeight data B)

/-- The conjugation action of the specified ambient quotient A/Z is used
on both sides; centrality makes its action on the original base defined. -/
theorem liftedBijection_quotientActor (a : QuotientA Z)
    (equivariantDown : ∀ phi phi' : DownBrauer data B,
      phi'.val = IrreducibleBrauerCharacter.twist root phi.val (quotientAction G Z a⁻¹) →
      (omegaDown phi').val = CharacterWeight.rightTwistConjugacyClass
        (quotientAction G Z a⁻¹) (omegaDown phi).val)
    (theta theta' : UpBrauer data B)
    (hTheta : theta'.val = IrreducibleBrauerCharacter.twist (upRoot _ hZ root)
      theta.val (originalQuotientAction G Z hZG hcentral a⁻¹)) :
    (liftedBijection data B omegaDown theta').val = CharacterWeight.rightTwistConjugacyClass
      (originalQuotientAction G Z hZG hcentral a⁻¹) (liftedBijection data B omegaDown theta).val :=
  liftedBijection_twist data B omegaDown _ _
    (originalQuotientAction_square G Z hZG hcentral a⁻¹) equivariantDown theta theta' hTheta

variable (hb : IsPrincipal B)

def principalStable (a : A) (theta : UpBrauer data B) :
    Supported (upRoot (kernelInG G Z) hZ root) B
      (TypeBCentralKernelInertia.conjugationOp G a • theta.val) :=
  principal_supported_twist data B hb (originalAction G a⁻¹) theta

variable (equivariantDown : ∀ (a : QuotientA Z) (phi phi' : DownBrauer data B),
  phi'.val = IrreducibleBrauerCharacter.twist root phi.val (quotientAction G Z a⁻¹) →
  (omegaDown phi').val = CharacterWeight.rightTwistConjugacyClass
    (quotientAction G Z a⁻¹) (omegaDown phi).val)

include equivariantDown in
/-- Equivariance of the constructed principal map for the original ambient
conjugation, inherited from the specified quotient actor alone. -/
theorem liftedMap_ambientAction (a : A) (theta : UpBrauer data B) :
    liftedMap data B omegaDown
      (TypeBCentralKernelInertia.fibreAction G (upRoot _ hZ root) B
        (principalStable G Z hZ hcentral root data B hb) a theta) =
      TypeBCentralKernelInertia.conjugationOp G a • liftedMap data B omegaDown theta := by
  apply liftedBijection_twist data B omegaDown
    (originalAction G a⁻¹) (quotientAction G Z (qA Z a)⁻¹)
  · intro g
    change qG G Z (originalAction G a⁻¹ g) =
      quotientAction G Z (qA Z a)⁻¹ (qG G Z g)
    simpa only [map_inv] using (quotientAction_mk G Z a⁻¹ g).symm
  · exact equivariantDown (qA Z a)
  · rfl

include hb equivariantDown in
/-- The raw-weight inertia inclusion uses the newly constructed upstairs
map, not a separately supplied upstairs matching. -/
theorem lifted_U_le_T (theta : UpBrauer data B) (W : CharacterWeight p K G)
    (representative : liftedMap data B omegaDown theta = TypeBCentralKernelInertia.classOf W) :
    TypeBCentralKernelInertia.U G W ≤ TypeBCentralKernelInertia.T G (upRoot _ hZ root) theta.val :=
  TypeBCentralKernelInertia.U_le_T G (upRoot _ hZ root) B
    (principalStable G Z hZ hcentral root data B hb) (liftedMap data B omegaDown)
    (liftedMap_injective data B omegaDown)
    (liftedMap_ambientAction G Z hZ hcentral root data B omegaDown hb equivariantDown)
    theta W representative

include hb equivariantDown in
open scoped Pointwise in
theorem lifted_T_eq_base_mul_U (theta : UpBrauer data B) (W : CharacterWeight p K G)
    (representative : liftedMap data B omegaDown theta = TypeBCentralKernelInertia.classOf W) :
    (TypeBCentralKernelInertia.T G (upRoot _ hZ root) theta.val : Set A) =
      (G : Set A) * (TypeBCentralKernelInertia.U G W : Set A) :=
  TypeBCentralKernelInertia.T_eq_base_mul_U G (upRoot _ hZ root) B
    (principalStable G Z hZ hcentral root data B hb) (liftedMap data B omegaDown)
    (liftedMap_injective data B omegaDown)
    (liftedMap_ambientAction G Z hZ hcentral root data B omegaDown hb equivariantDown)
    theta W representative

end Ambient

end ModularRep.PaperProofs.TypeBCentralKernelFibreAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
