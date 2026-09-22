import ModularRep.PaperProofs.TypeBSpinDiagonalFieldQuotient
import ModularRep.PaperProofs.TypeBSpinFieldClassActions
import Mathlib.GroupTheory.NoncommCoprod

/-!
# The actual effective product actions on Spin classes

The literal quotient actions are transported along the prescribed diagonal
quotient equivalence. Their commutation with field pullback is proved from
the actual conjugation square and the proved field invariance of the
quotient. `MonoidHom.noncommCoprod` then constructs the product actions on
exact K0, primitive blocks, ordinary characters and prescribed-root Brauer
characters. The target endomorphism and permutation monoids are not assumed
commutative.

The only diagonal input is the existing literal homomorphism, its
surjectivity and its exact kernel. No class action, commutation equation,
effective-action source, rational-series stability or target is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinEffectiveClassActions

open ModularRep ExactGrothendieckGroup TypeBCliffordCarriers TypeBSpinStabilizer
open TypeBSpinInnerClassActions TypeBSpinQuotientClassActions
open TypeBSpinFieldClassActions TypeBSpinDiagonalFieldQuotient

universe u

variable {n : ℕ} {F : Type} [Field F] (N : NormSource n F) (D : DiagonalSource N)

/-- Transport the actual quotient homomorphism through the same diagonal isomorphism. -/
def diagonalLift {M : Type u} [Monoid M]
    (rho : TypeBSpinQuotientClassActions.Quotient N →* M) : DiagonalGroup →* M :=
  rho.comp (D.quotientEquiv N).symm.toMonoidHom

@[simp] theorem diagonalLift_diagonal {M : Type u} [Monoid M]
    (rho : TypeBSpinQuotientClassActions.Quotient N →* M) (g : SpecialClifford n F) :
    diagonalLift N D rho (D.diagonal g) = rho (projection N g) := by
  change rho ((D.quotientEquiv N).symm (D.diagonal g)) = rho (projection N g)
  rw [← D.quotientEquiv_mk N g, MulEquiv.symm_apply_apply]

variable {p f : ℕ} [Finite F] [CharP F p]
  {parameters : OddFieldParameters F p f}
  (fs : FieldActionSource n F p f parameters N)

/-- Covariance on actual Clifford representatives becomes commutation after descent.
The applications below supply the checked representation/character squares. -/
theorem diagonalLift_commute {M : Type u} [Monoid M]
    (rho : TypeBSpinQuotientClassActions.Quotient N →* M)
    (field : FieldGroup f →* M)
    (covariance : ∀ (e : FieldGroup f) (g : SpecialClifford n F),
      field e * rho (projection N g) =
        rho (projection N (fs.action e g)) * field e)
    (d : DiagonalGroup) (e : FieldGroup f) :
    Commute (diagonalLift N D rho d) (field e) := by
  obtain ⟨g, rfl⟩ := D.surjective d
  rw [diagonalLift_diagonal]
  change rho (projection N g) * field e = field e * rho (projection N g)
  symm
  calc
    field e * rho (projection N g) =
        rho (projection N (fs.action e g)) * field e := covariance e g
    _ = rho (projection N g) * field e := by rw [projection_field N fs D e g]

variable {k : Type} [Field k]

/-- Effective product representation on exact K0 over the actual coefficient field. -/
def effectiveKZeroAction : Representation ℤ (OuterGroup f) (FDRepKZero k (Spin n F N)) :=
  MonoidHom.noncommCoprod
    (diagonalLift N D (quotientKZeroAction (k := k) N))
    (spinFieldKZeroAction (k := k) fs)
    (diagonalLift_commute N D fs (quotientKZeroAction (k := k) N)
      (spinFieldKZeroAction (k := k) fs)
      (fun e g => spinFieldKZeroAction_intertwines (k := k) fs e g))

@[simp] theorem effectiveKZeroAction_apply (d : DiagonalGroup) (e : FieldGroup f)
    (x : FDRepKZero k (Spin n F N)) :
    effectiveKZeroAction (k := k) N D fs (d, e) x =
      quotientKZeroAction (k := k) N ((D.quotientEquiv N).symm d)
        (spinFieldKZeroAction (k := k) fs e x) := rfl

@[simp] theorem effectiveKZeroAction_diagonal (g : SpecialClifford n F) :
    effectiveKZeroAction (k := k) N D fs (D.diagonal g, 1) =
      spinKZeroAction (k := k) N g := by
  change diagonalLift N D (quotientKZeroAction (k := k) N) (D.diagonal g) *
    spinFieldKZeroAction (k := k) fs 1 = spinKZeroAction (k := k) N g
  rw [diagonalLift_diagonal, map_one, mul_one, quotientKZeroAction_mk]

theorem effectiveKZeroAction_diagonal_apply (g : SpecialClifford n F)
    (x : FDRepKZero k (Spin n F N)) :
    effectiveKZeroAction (k := k) N D fs (D.diagonal g, 1) x =
      twistKZero (k := k) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) x := by
  rw [effectiveKZeroAction_diagonal]
  rfl

@[simp] theorem effectiveKZeroAction_field (e : FieldGroup f) :
    effectiveKZeroAction (k := k) N D fs (1, e) = spinFieldKZeroAction (k := k) fs e := by
  change diagonalLift N D (quotientKZeroAction (k := k) N) 1 *
    spinFieldKZeroAction (k := k) fs e = spinFieldKZeroAction (k := k) fs e
  rw [map_one, one_mul]

theorem effectiveKZeroAction_field_apply (e : FieldGroup f)
    (x : FDRepKZero k (Spin n F N)) :
    effectiveKZeroAction (k := k) N D fs (1, e) x =
      twistKZero (k := k) (spinFieldAction n F fs e⁻¹) x := by
  rw [effectiveKZeroAction_field]
  rfl

/-- Effective product permutation of actual primitive central idempotents. -/
def effectiveBlockHom : OuterGroup f →* Equiv.Perm (LiteralPrimitiveBlock k (Spin n F N)) :=
  MonoidHom.noncommCoprod
    (diagonalLift N D (quotientBlockHom (k := k) N))
    (spinFieldBlockHom (k := k) fs)
    (diagonalLift_commute N D fs (quotientBlockHom (k := k) N)
      (spinFieldBlockHom (k := k) fs)
      (fun e g => spinFieldBlockHom_intertwines (k := k) fs e g))

@[simp] theorem effectiveBlockHom_apply (d : DiagonalGroup) (e : FieldGroup f)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    effectiveBlockHom (k := k) N D fs (d, e) b =
      quotientBlockHom (k := k) N ((D.quotientEquiv N).symm d)
        (spinFieldBlockHom (k := k) fs e b) := rfl

@[simp] theorem effectiveBlockHom_diagonal (g : SpecialClifford n F) :
    effectiveBlockHom (k := k) N D fs (D.diagonal g, 1) = spinBlockHom (k := k) N g := by
  change diagonalLift N D (quotientBlockHom (k := k) N) (D.diagonal g) *
    spinFieldBlockHom (k := k) fs 1 = spinBlockHom (k := k) N g
  rw [diagonalLift_diagonal, map_one, mul_one, quotientBlockHom_mk]

theorem effectiveBlockHom_diagonal_apply (g : SpecialClifford n F)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    effectiveBlockHom (k := k) N D fs (D.diagonal g, 1) b =
      LiteralPrimitiveBlock.rightTwistBlock b
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := by
  rw [effectiveBlockHom_diagonal]
  rfl

@[simp] theorem effectiveBlockHom_field (e : FieldGroup f) :
    effectiveBlockHom (k := k) N D fs (1, e) = spinFieldBlockHom (k := k) fs e := by
  change diagonalLift N D (quotientBlockHom (k := k) N) 1 *
    spinFieldBlockHom (k := k) fs e = spinFieldBlockHom (k := k) fs e
  rw [map_one, one_mul]

theorem effectiveBlockHom_field_apply (e : FieldGroup f)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    effectiveBlockHom (k := k) N D fs (1, e) b =
      LiteralPrimitiveBlock.rightTwistBlock b (spinFieldAction n F fs e⁻¹) := by
  rw [effectiveBlockHom_field]
  rfl

section Ordinary

variable [CharZero k]

/-- Effective product permutation of the same function-valued ordinary Irr. -/
def effectiveOrdinaryHom :
    OuterGroup f →* Equiv.Perm (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :=
  MonoidHom.noncommCoprod
    (diagonalLift N D (quotientOrdinaryHom (k := k) N))
    (spinFieldOrdinaryHom (k := k) fs)
    (diagonalLift_commute N D fs (quotientOrdinaryHom (k := k) N)
      (spinFieldOrdinaryHom (k := k) fs)
      (fun e g => spinFieldOrdinaryHom_intertwines (k := k) fs e g))

@[simp] theorem effectiveOrdinaryHom_apply (d : DiagonalGroup) (e : FieldGroup f)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    effectiveOrdinaryHom (k := k) N D fs (d, e) chi =
      quotientOrdinaryHom (k := k) N ((D.quotientEquiv N).symm d)
        (spinFieldOrdinaryHom (k := k) fs e chi) := rfl

@[simp] theorem effectiveOrdinaryHom_diagonal (g : SpecialClifford n F) :
    effectiveOrdinaryHom (k := k) N D fs (D.diagonal g, 1) = spinOrdinaryHom (k := k) N g := by
  change diagonalLift N D (quotientOrdinaryHom (k := k) N) (D.diagonal g) *
    spinFieldOrdinaryHom (k := k) fs 1 = spinOrdinaryHom (k := k) N g
  rw [diagonalLift_diagonal, map_one, mul_one, quotientOrdinaryHom_mk]

theorem effectiveOrdinaryHom_diagonal_apply (g : SpecialClifford n F)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    effectiveOrdinaryHom (k := k) N D fs (D.diagonal g, 1) chi =
      OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := by
  rw [effectiveOrdinaryHom_diagonal]
  rfl

@[simp] theorem effectiveOrdinaryHom_field (e : FieldGroup f) :
    effectiveOrdinaryHom (k := k) N D fs (1, e) = spinFieldOrdinaryHom (k := k) fs e := by
  change diagonalLift N D (quotientOrdinaryHom (k := k) N) 1 *
    spinFieldOrdinaryHom (k := k) fs e = spinFieldOrdinaryHom (k := k) fs e
  rw [map_one, one_mul]

theorem effectiveOrdinaryHom_field_apply (e : FieldGroup f)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    effectiveOrdinaryHom (k := k) N D fs (1, e) chi =
      OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
        (spinFieldAction n F fs e⁻¹) := by
  rw [effectiveOrdinaryHom_field]
  rfl

end Ordinary

section Brauer

variable {ell : ℕ} {K : Type} [Field K] [CharZero K]
  [CharP k ell] [IsAlgClosed k] [Finite (Spin n F N)]
  (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- Effective product permutation of Brauer characters with the prescribed root. -/
def effectiveBrauerHom : OuterGroup f →* Equiv.Perm (IBr iota) :=
  MonoidHom.noncommCoprod
    (diagonalLift N D (quotientBrauerHom N iota))
    (spinFieldBrauerHom fs iota)
    (diagonalLift_commute N D fs (quotientBrauerHom N iota)
      (spinFieldBrauerHom fs iota)
      (fun e g => spinFieldBrauerHom_intertwines fs iota e g))

@[simp] theorem effectiveBrauerHom_apply (d : DiagonalGroup) (e : FieldGroup f)
    (phi : IBr iota) :
    effectiveBrauerHom N D fs iota (d, e) phi =
      quotientBrauerHom N iota ((D.quotientEquiv N).symm d)
        (spinFieldBrauerHom fs iota e phi) := rfl

@[simp] theorem effectiveBrauerHom_diagonal (g : SpecialClifford n F) :
    effectiveBrauerHom N D fs iota (D.diagonal g, 1) = spinBrauerHom N iota g := by
  change diagonalLift N D (quotientBrauerHom N iota) (D.diagonal g) *
    spinFieldBrauerHom fs iota 1 = spinBrauerHom N iota g
  rw [diagonalLift_diagonal, map_one, mul_one, quotientBrauerHom_mk]

theorem effectiveBrauerHom_diagonal_apply (g : SpecialClifford n F) (phi : IBr iota) :
    effectiveBrauerHom N D fs iota (D.diagonal g, 1) phi =
      IrreducibleBrauerCharacter.twist iota phi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := by
  rw [effectiveBrauerHom_diagonal]
  rfl

@[simp] theorem effectiveBrauerHom_field (e : FieldGroup f) :
    effectiveBrauerHom N D fs iota (1, e) = spinFieldBrauerHom fs iota e := by
  change diagonalLift N D (quotientBrauerHom N iota) 1 *
    spinFieldBrauerHom fs iota e = spinFieldBrauerHom fs iota e
  rw [map_one, one_mul]

theorem effectiveBrauerHom_field_apply (e : FieldGroup f) (phi : IBr iota) :
    effectiveBrauerHom N D fs iota (1, e) phi =
      IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F fs e⁻¹) := by
  rw [effectiveBrauerHom_field]
  rfl

end Brauer

end ModularRep.PaperProofs.TypeBSpinEffectiveClassActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
