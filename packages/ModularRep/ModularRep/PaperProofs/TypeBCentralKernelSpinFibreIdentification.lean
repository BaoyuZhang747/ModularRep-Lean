import ModularRep.PaperProofs.TypeBCentralKernelButterflyCharacterIdentification
import ModularRep.PaperProofs.TypeBCentralKernelSourceAssembly
import ModularRep.PaperProofs.TypeBCentralKernelWeightTransport

/-!
# Literal sets of Spin and Omega characters and weights

Primitive blocks are transported by the actual group-basis ring equivalence.
The trivial representation detects the same principal block, and supported
irreducible Brauer characters give equivalent literal block fibres. Prescribed
roots are retained: equality of their full lift functions identifies the
root embeddings, rather than replacing an existing root by a new parameter.

Ordinary character weights use the checked normalizer-quotient transport for
an isomorphism, whose kernel is proved trivial. Their raw representatives,
local character values, conjugacy classes and automorphism actions are given
on the actual Spin and Omega equivalences. No block allocation on weights or
Brauer-to-weight correspondence is an input or a conclusion of this file.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification

open ModularRep TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelButterflyCertificate TypeBCentralKernelInertia

universe u

section Blocks

variable {k X Y : Type u} [Field k] [Group X] [Finite X] [Group Y] [Finite Y]

/-- The equivalence of actual primitive central idempotents induced by a
group equivalence. Its map is exactly the Butterfly certificate's map. -/
def primitiveBlockEquiv (e : X ≃* Y) :
    LiteralPrimitiveBlock k X ≃ LiteralPrimitiveBlock k Y where
  toFun := blockAlong e
  invFun := blockAlong e.symm
  left_inv b := by
    apply Subtype.ext
    change (MonoidAlgebra.mapDomainRingEquiv k e).symm
      (MonoidAlgebra.mapDomainRingEquiv k e b.val) = b.val
    exact (MonoidAlgebra.mapDomainRingEquiv k e).symm_apply_apply b.val
  right_inv b := by
    apply Subtype.ext
    change MonoidAlgebra.mapDomainRingEquiv k e
      ((MonoidAlgebra.mapDomainRingEquiv k e).symm b.val) = b.val
    exact (MonoidAlgebra.mapDomainRingEquiv k e).apply_symm_apply b.val

@[simp] theorem primitiveBlockEquiv_val (e : X ≃* Y)
    (b : LiteralPrimitiveBlock k X) :
    (primitiveBlockEquiv e b).val = MonoidAlgebra.mapDomainRingEquiv k e b.val := rfl

/-- Principalness is preserved because the same trivial representation
evaluates the transported group algebra element. -/
theorem primitiveBlockEquiv_principal_iff (e : X ≃* Y)
    (b : LiteralPrimitiveBlock k X) :
    IsPrincipal (primitiveBlockEquiv e b) ↔ IsPrincipal b := by
  have h := Representation.pullback_asAlgebraHom_domCongr_apply
    (1 : Representation k X k) e b.val
  change (1 : Representation k Y k).asAlgebraHom
    (MonoidAlgebra.mapDomainRingEquiv k e b.val) =
      (1 : Representation k X k).asAlgebraHom b.val at h
  change (1 : Representation k Y k).asAlgebraHom
    (MonoidAlgebra.mapDomainRingEquiv k e b.val) = 1 ↔
      (1 : Representation k X k).asAlgebraHom b.val = 1
  rw [h]

end Blocks

section Brauer

variable {p : ℕ} {k K X Y : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group X] [Finite X] [Group Y] [Finite Y]

/-- On one fixed group, the full lift determines the chosen root embedding. -/
theorem root_eq_of_lift_eq (iota j : PrimeRegularRootEmbedding p k K X)
    (lifts : iota.lift = j.lift) : iota = j := by
  have he : iota.toMulEquiv = j.toMulEquiv := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Units.ext
    exact (iota.lift_coe z).symm.trans
      ((congrFun lifts ((z : kˣ) : k)).trans (j.lift_coe z))
  cases iota
  cases j
  cases he
  rfl

/-- Transport to the prescribed target root, rather than a twice-transported
root. The only guard is equality of the actual field-level lift functions. -/
def brauerEquiv (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (lifts : iotaY.lift = iotaX.lift) : IBr iotaX ≃ IBr iotaY := by
  have hroot : iotaX.alongMulEquiv e = iotaY :=
    root_eq_of_lift_eq _ _ ((funext (iotaX.alongMulEquiv_lift e)).trans lifts.symm)
  exact (IrreducibleBrauerCharacter.equivAlongMulEquiv iotaX e).trans
    (Equiv.cast (congrArg (fun iota => IBr iota) hroot))

@[simp] theorem brauerEquiv_val (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (lifts : iotaY.lift = iotaX.lift) (theta : IBr iotaX) :
    (brauerEquiv e iotaX iotaY lifts theta).val =
      PrimeRegularClassFunction.pullback e.symm.toMonoidHom theta.val := by
  have hroot : iotaX.alongMulEquiv e = iotaY :=
    root_eq_of_lift_eq _ _ ((funext (iotaX.alongMulEquiv_lift e)).trans lifts.symm)
  subst iotaY
  rfl

/-- Both directions use support by an actual irreducible representation. -/
theorem supported_brauerEquiv_iff (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (lifts : iotaY.lift = iotaX.lift)
    (b : LiteralPrimitiveBlock k X) (theta : IBr iotaX) :
    Supported iotaY (primitiveBlockEquiv e b)
      (brauerEquiv e iotaX iotaY lifts theta) ↔ Supported iotaX b theta := by
  constructor
  · intro h
    have values : theta.val = PrimeRegularClassFunction.pullback e.toMonoidHom
        (brauerEquiv e iotaX iotaY lifts theta).val := by
      rw [brauerEquiv_val]
      apply PrimeRegularClassFunction.ext
      intro x
      change theta.val x = theta.val
        (PrimeRegularElement.map e.symm.toMonoidHom
          (PrimeRegularElement.map e.toMonoidHom x))
      congr 1
      apply Subtype.ext
      exact (e.symm_apply_apply x.val).symm
    have support :=
      TypeBCentralKernelButterflyCharacterIdentification.supported_along_of_lift_eq
        e.symm iotaY iotaX (primitiveBlockEquiv e b)
        (brauerEquiv e iotaX iotaY lifts theta) theta lifts.symm values h
    have inverse : blockAlong e.symm (primitiveBlockEquiv e b) = b :=
      (primitiveBlockEquiv (k := k) e).symm_apply_apply b
    exact inverse ▸ support
  · intro h
    exact TypeBCentralKernelButterflyCharacterIdentification.supported_along_of_lift_eq
      e iotaX iotaY b theta (brauerEquiv e iotaX iotaY lifts theta)
      lifts (brauerEquiv_val e iotaX iotaY lifts theta) h

/-- Restriction to a specified actual primitive block, with no character
or block correspondence source. -/
def brauerFibreEquiv (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (lifts : iotaY.lift = iotaX.lift) (b : LiteralPrimitiveBlock k X) :
    BrauerFibre iotaX b ≃ BrauerFibre iotaY (primitiveBlockEquiv e b) :=
  (brauerEquiv e iotaX iotaY lifts).subtypeEquiv
    (fun theta => (supported_brauerEquiv_iff e iotaX iotaY lifts b theta).symm)

@[simp] theorem brauerFibreEquiv_val (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (lifts : iotaY.lift = iotaX.lift) (b : LiteralPrimitiveBlock k X)
    (theta : BrauerFibre iotaX b) :
    (brauerFibreEquiv e iotaX iotaY lifts b theta).val.val =
      PrimeRegularClassFunction.pullback e.symm.toMonoidHom theta.val.val :=
  brauerEquiv_val e iotaX iotaY lifts theta.val

/-- Naturality for the actual displayed automorphism square. -/
theorem brauerEquiv_twist (e : X ≃* Y)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (lifts : iotaY.lift = iotaX.lift)
    (alpha : MulAut X) (beta : MulAut Y)
    (square : ∀ x, e (alpha x) = beta (e x)) (theta : IBr iotaX) :
    brauerEquiv e iotaX iotaY lifts (IrreducibleBrauerCharacter.twist iotaX theta alpha) =
      IrreducibleBrauerCharacter.twist iotaY
        (brauerEquiv e iotaX iotaY lifts theta) beta := by
  apply Subtype.ext
  rw [brauerEquiv_val, IrreducibleBrauerCharacter.val_twist,
    IrreducibleBrauerCharacter.val_twist, brauerEquiv_val]
  apply PrimeRegularClassFunction.ext
  intro y
  change theta.val (PrimeRegularElement.map alpha.toMonoidHom
      (PrimeRegularElement.map e.symm.toMonoidHom y)) =
    theta.val (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map beta.toMonoidHom y))
  congr 1
  apply Subtype.ext
  apply e.injective
  change e (alpha (e.symm y.val)) = e (e.symm (beta y.val))
  simpa only [e.apply_symm_apply] using square (e.symm y.val)

end Brauer

section Weights

variable {p : ℕ} {K X Y : Type u}
  [Field K] [CharZero K] [Group X] [Finite X] [Group Y] [Finite Y]

/-- The normal prime-kernel transport applies to an equivalence because its
literal homomorphism kernel is the trivial subgroup. -/
theorem equivKernel_isPGroup (e : X ≃* Y) : IsPGroup p e.toMonoidHom.ker := by
  rw [e.toMonoidHom.ker_eq_bot e.injective]
  exact IsPGroup.of_bot

def rawWeightEquiv (e : X ≃* Y) : CharacterWeight p K X ≃ CharacterWeight p K Y :=
  TypeBCentralKernelWeightTransport.weightEquiv e.toMonoidHom e.surjective
    (equivKernel_isPGroup (p := p) e)

def weightClassEquiv (e : X ≃* Y) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X) ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := Y) :=
  TypeBCentralKernelWeightTransport.conjugacyClassEquiv e.toMonoidHom e.surjective
    (equivKernel_isPGroup (p := p) e)

@[simp] theorem rawWeightEquiv_subgroup (e : X ≃* Y) (W : CharacterWeight p K X) :
    (rawWeightEquiv e W).subgroup = W.subgroup.map e.toMonoidHom := rfl

/-- Local ordinary characters agree on the actual normalizer representatives
and the actual quotient maps used to define weights. -/
theorem rawWeightEquiv_localCharacter (e : X ≃* Y) (W : CharacterWeight p K X)
    (x : Subgroup.normalizer (W.subgroup : Set X))
    (y : Subgroup.normalizer ((rawWeightEquiv e W).subgroup : Set Y))
    (hxy : e x = y) :
    (rawWeightEquiv e W).localCharacter
        (TypeBCentralKernelWeightTransport.localMk (rawWeightEquiv e W).subgroup y) =
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup x) :=
  TypeBCentralKernelWeightTransport.descend_localCharacter e.toMonoidHom e.surjective
    (equivKernel_isPGroup (p := p) e) W x y hxy

@[simp] theorem weightClassEquiv_classOf (e : X ≃* Y) (W : CharacterWeight p K X) :
    weightClassEquiv e (classOf W) = classOf (rawWeightEquiv e W) := rfl

theorem rawWeightEquiv_rightTwist (e : X ≃* Y)
    (alpha : MulAut X) (beta : MulAut Y)
    (square : ∀ x, e (alpha x) = beta (e x)) (W : CharacterWeight p K X) :
    rawWeightEquiv e (W.rightTwist alpha) = (rawWeightEquiv e W).rightTwist beta :=
  TypeBCentralKernelWeightTransport.descend_rightTwist e.toMonoidHom e.surjective
    (equivKernel_isPGroup (p := p) e) alpha beta square W

theorem weightClassEquiv_rightTwist (e : X ≃* Y)
    (alpha : MulAut X) (beta : MulAut Y)
    (square : ∀ x, e (alpha x) = beta (e x))
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X)) :
    weightClassEquiv e (CharacterWeight.rightTwistConjugacyClass alpha w) =
      CharacterWeight.rightTwistConjugacyClass beta (weightClassEquiv e w) :=
  TypeBCentralKernelWeightTransport.conjugacyClassEquiv_rightTwist
    e.toMonoidHom e.surjective (equivKernel_isPGroup (p := p) e) alpha beta square w

end Weights

section Spin

open TypeBCliffordCarriers TypeBAutomorphismSource TypeBWeightStabilizerSource TypeBSpinCoverSource
open TypeBCentralKernelCarriers TypeBCentralKernelBrauerInflation

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} {parameters : OddFieldParameters F r f}
  (S : FieldActionSource n F r f parameters N)
  [Finite (TypeBCentralKernelSpinBinding.A S)] [Finite (Spin n F N)]

variable {k0 K0 : Type} [Field k0] [Field K0] [CharP k0 2]
  [IsAlgClosed k0] [CharZero K0] [IsAlgClosed K0]

/-- This is exactly the root already used in `SpinTransportData` upstairs. -/
abbrev embeddedSpinRoot
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :=
  upRoot (kernelInG (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S))
    (TypeBCentralKernelSpinBinding.kernel_isTwoGroup S centre rank)
    (TypeBCentralKernelSourceAssembly.spinQuotientRoot S omegaRoot)

/-- The root on literal Spin is obtained from that same prescribed upstairs
root through the actual Spin embedding equivalence. -/
def literalSpinRoot
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :
    PrimeRegularRootEmbedding 2 k0 K0 (Spin n F N) :=
  (embeddedSpinRoot S centre rank omegaRoot).alongMulEquiv
    (TypeBCentralKernelSpinBinding.spinEquiv S).symm

theorem literalSpinRoot_lift
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :
    (embeddedSpinRoot S centre rank omegaRoot).lift =
      (literalSpinRoot S centre rank omegaRoot).lift :=
  (funext ((embeddedSpinRoot S centre rank omegaRoot).alongMulEquiv_lift
    (TypeBCentralKernelSpinBinding.spinEquiv S).symm)).symm

def spinPrimitiveBlockEquiv :
    LiteralPrimitiveBlock k0 (Spin n F N) ≃
      LiteralPrimitiveBlock k0 (TypeBCentralKernelSpinBinding.G S) :=
  primitiveBlockEquiv (TypeBCentralKernelSpinBinding.spinEquiv S)

def omegaPrimitiveBlockEquiv :
    LiteralPrimitiveBlock k0 (Omega N) ≃ LiteralPrimitiveBlock k0
      (QuotientG (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S)) :=
  primitiveBlockEquiv (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S)

theorem spinPrimitiveBlockEquiv_principal_iff (b : LiteralPrimitiveBlock k0 (Spin n F N)) :
    IsPrincipal (spinPrimitiveBlockEquiv S b) ↔ IsPrincipal b :=
  primitiveBlockEquiv_principal_iff (TypeBCentralKernelSpinBinding.spinEquiv S) b

theorem omegaPrimitiveBlockEquiv_principal_iff (b : LiteralPrimitiveBlock k0 (Omega N)) :
    IsPrincipal (omegaPrimitiveBlockEquiv S b) ↔ IsPrincipal b :=
  primitiveBlockEquiv_principal_iff (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S) b

def spinBrauerEquiv
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :
    IBr (literalSpinRoot S centre rank omegaRoot) ≃
      IBr (embeddedSpinRoot S centre rank omegaRoot) :=
  brauerEquiv (TypeBCentralKernelSpinBinding.spinEquiv S)
    (literalSpinRoot S centre rank omegaRoot) (embeddedSpinRoot S centre rank omegaRoot)
    (literalSpinRoot_lift S centre rank omegaRoot)

def omegaBrauerEquiv (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N)) :
    IBr omegaRoot ≃ IBr (TypeBCentralKernelSourceAssembly.spinQuotientRoot S omegaRoot) :=
  brauerEquiv (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S) omegaRoot
    (TypeBCentralKernelSourceAssembly.spinQuotientRoot S omegaRoot)
    (funext (TypeBCentralKernelSourceAssembly.spinQuotientRoot_lift S omegaRoot))

def spinBrauerFibreEquiv
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N))
    (b : LiteralPrimitiveBlock k0 (Spin n F N)) :
    BrauerFibre (literalSpinRoot S centre rank omegaRoot) b ≃
      BrauerFibre (embeddedSpinRoot S centre rank omegaRoot) (spinPrimitiveBlockEquiv S b) :=
  brauerFibreEquiv (TypeBCentralKernelSpinBinding.spinEquiv S)
    (literalSpinRoot S centre rank omegaRoot) (embeddedSpinRoot S centre rank omegaRoot)
    (literalSpinRoot_lift S centre rank omegaRoot) b

def omegaBrauerFibreEquiv (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N))
    (b : LiteralPrimitiveBlock k0 (Omega N)) :
    BrauerFibre omegaRoot b ≃
      BrauerFibre (TypeBCentralKernelSourceAssembly.spinQuotientRoot S omegaRoot)
        (omegaPrimitiveBlockEquiv S b) :=
  brauerFibreEquiv (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S) omegaRoot
    (TypeBCentralKernelSourceAssembly.spinQuotientRoot S omegaRoot)
    (funext (TypeBCentralKernelSourceAssembly.spinQuotientRoot_lift S omegaRoot)) b

def spinRawWeightEquiv : CharacterWeight 2 K0 (Spin n F N) ≃
    CharacterWeight 2 K0 (TypeBCentralKernelSpinBinding.G S) :=
  rawWeightEquiv (TypeBCentralKernelSpinBinding.spinEquiv S)

def omegaRawWeightEquiv : CharacterWeight 2 K0 (Omega N) ≃
    CharacterWeight 2 K0
      (QuotientG (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S)) :=
  rawWeightEquiv (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S)

def spinWeightClassEquiv :
    CharacterWeight.ConjugacyClass (p := 2) (K := K0) (G := Spin n F N) ≃
      CharacterWeight.ConjugacyClass (p := 2) (K := K0)
        (G := TypeBCentralKernelSpinBinding.G S) :=
  weightClassEquiv (TypeBCentralKernelSpinBinding.spinEquiv S)

def omegaWeightClassEquiv :
    CharacterWeight.ConjugacyClass (p := 2) (K := K0) (G := Omega N) ≃
      CharacterWeight.ConjugacyClass (p := 2) (K := K0)
        (G := QuotientG (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S)) :=
  weightClassEquiv (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S)

/-- Brauer-character naturality uses the given special-Clifford/field
ambient action, without replacing it by the full automorphism group. -/
theorem spinBrauerEquiv_twist
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (rank : 3 ≤ n) (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N))
    (a : TypeBCentralKernelSpinBinding.A S)
    (theta : IBr (literalSpinRoot S centre rank omegaRoot)) :
    spinBrauerEquiv S centre rank omegaRoot
        (IrreducibleBrauerCharacter.twist _ theta (ambientAutomorphism S a)) =
      IrreducibleBrauerCharacter.twist _ (spinBrauerEquiv S centre rank omegaRoot theta)
        (originalAction (TypeBCentralKernelSpinBinding.G S) a) :=
  brauerEquiv_twist (TypeBCentralKernelSpinBinding.spinEquiv S)
    (literalSpinRoot S centre rank omegaRoot) (embeddedSpinRoot S centre rank omegaRoot)
    (literalSpinRoot_lift S centre rank omegaRoot) (ambientAutomorphism S a)
    (originalAction (TypeBCentralKernelSpinBinding.G S) a)
    (TypeBCentralKernelSpinBinding.spinEquiv_action S a) theta

theorem omegaBrauerEquiv_twist
    (omegaRoot : PrimeRegularRootEmbedding 2 k0 K0 (Omega N))
    (a : QuotientA (TypeBCentralKernelSpinBinding.P S)) (theta : IBr omegaRoot) :
    omegaBrauerEquiv S omegaRoot
        (IrreducibleBrauerCharacter.twist _ theta (TypeBCentralKernelSpinBinding.omegaAction S a)) =
      IrreducibleBrauerCharacter.twist _ (omegaBrauerEquiv S omegaRoot theta)
        (quotientAction (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S) a) :=
  brauerEquiv_twist (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S) omegaRoot
    (TypeBCentralKernelSourceAssembly.spinQuotientRoot S omegaRoot)
    (funext (TypeBCentralKernelSourceAssembly.spinQuotientRoot_lift S omegaRoot))
    (TypeBCentralKernelSpinBinding.omegaAction S a)
    (quotientAction (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S) a)
    (TypeBCentralKernelSpinBinding.omegaAction_equiv S a) theta

theorem spinWeightClassEquiv_rightTwist (a : TypeBCentralKernelSpinBinding.A S)
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K0) (G := Spin n F N)) :
    spinWeightClassEquiv S (CharacterWeight.rightTwistConjugacyClass (ambientAutomorphism S a) w) =
      CharacterWeight.rightTwistConjugacyClass
        (originalAction (TypeBCentralKernelSpinBinding.G S) a) (spinWeightClassEquiv S w) :=
  weightClassEquiv_rightTwist (TypeBCentralKernelSpinBinding.spinEquiv S)
    (ambientAutomorphism S a) (originalAction (TypeBCentralKernelSpinBinding.G S) a)
    (TypeBCentralKernelSpinBinding.spinEquiv_action S a) w

theorem omegaWeightClassEquiv_rightTwist (a : QuotientA (TypeBCentralKernelSpinBinding.P S))
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K0) (G := Omega N)) :
    omegaWeightClassEquiv S
        (CharacterWeight.rightTwistConjugacyClass (TypeBCentralKernelSpinBinding.omegaAction S a) w) =
      CharacterWeight.rightTwistConjugacyClass
        (quotientAction (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S) a)
        (omegaWeightClassEquiv S w) :=
  weightClassEquiv_rightTwist (TypeBCentralKernelSpinBinding.omegaQuotientEquiv S)
    (TypeBCentralKernelSpinBinding.omegaAction S a)
    (quotientAction (TypeBCentralKernelSpinBinding.G S) (TypeBCentralKernelSpinBinding.P S) a)
    (TypeBCentralKernelSpinBinding.omegaAction_equiv S a) w

end Spin

end ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
