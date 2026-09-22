import ModularRep.PaperProofs.TypeBSpinQuotientClassActions

/-!
# Actual field actions and their covariance with Spin conjugation

The given Clifford field action restricts to the same norm-one Spin group.
Inverse pullback gives its actions on exact K0, primitive blocks, Brauer
characters and ordinary characters. One literal automorphism square proves
the covariance with actual special Clifford conjugation for every carrier.

No diagonal quotient identification, commutation after descent, rational-series
stability or new external source is supplied here. The only field source is
the existing `FieldActionSource` on the prescribed Clifford algebra and norm.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinFieldClassActions

open ModularRep ExactGrothendieckGroup TypeBCliffordCarriers TypeBSpinInnerClassActions
open TypeBSpinQuotientClassActions

universe u v

/-- A literal restriction square transports conjugation on a normal subgroup. -/
theorem normalConjugation_square {A : Type u} [Group A]
    (H : Subgroup A) [H.Normal] (alpha : MulAut A) (beta : MulAut H)
    (compatible : ∀ h : H, (beta h).val = alpha h.val) (g : A) :
    beta * MulAut.conjNormal (H := H) g =
      MulAut.conjNormal (H := H) (alpha g) * beta := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  change (beta (MulAut.conjNormal (H := H) g h)).val =
    alpha g * (beta h).val * (alpha g)⁻¹
  rw [compatible, compatible]
  change alpha (g * h.val * g⁻¹) = alpha g * alpha h.val * (alpha g)⁻¹
  simp only [map_mul, map_inv]

variable {n p f : ℕ} {F k : Type u} [Field F] [Finite F] [CharP F p]
  [Field k] {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (fs : FieldActionSource n F p f parameters N)

/-- Inverse field pullback is a homomorphism into the opposite automorphism group. -/
def spinInverseField : FieldGroup f →* (MulAut (Spin n F N))ᵐᵒᵖ where
  toFun e := MulOpposite.op (spinFieldAction n F fs e⁻¹)
  map_one' := by simp
  map_mul' e d := by simp

@[simp] theorem spinInverseField_apply (e : FieldGroup f) :
    (spinInverseField fs e).unop = spinFieldAction n F fs e⁻¹ := rfl

/-- The field automorphism transports actual Clifford conjugation on Spin. -/
theorem spinField_conjugation_square (e : FieldGroup f) (g : SpecialClifford n F) :
    spinFieldAction n F fs e * MulAut.conjNormal (H := SpinSubgroup n F N) g =
      MulAut.conjNormal (H := SpinSubgroup n F N) (fs.action e g) *
        spinFieldAction n F fs e :=
  normalConjugation_square (SpinSubgroup n F N) (fs.action e)
    (spinFieldAction n F fs e) (spinFieldAction_coe n F fs e) g

/-- The SAME square in the inverse/opposite convention used by class actions. -/
theorem spinInverseField_conjugation (e : FieldGroup f) (g : SpecialClifford n F) :
    spinInverseField fs e * spinInverseConjugation N g =
      spinInverseConjugation N (fs.action e g) * spinInverseField fs e := by
  apply MulOpposite.unop_injective
  change MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹ * spinFieldAction n F fs e⁻¹ =
    spinFieldAction n F fs e⁻¹ *
      MulAut.conjNormal (H := SpinSubgroup n F N) (fs.action e g)⁻¹
  have h := spinField_conjugation_square fs e⁻¹ (fs.action e g⁻¹)
  have cancel : fs.action e⁻¹ (fs.action e g⁻¹) = g⁻¹ := by
    rw [map_inv]
    exact (fs.action e).symm_apply_apply g⁻¹
  rw [cancel] at h
  simpa only [map_inv] using h.symm

/-- Every homomorphism out of the actual opposite actor preserves this square. -/
theorem spinField_map_covariant {M : Type v} [Monoid M]
    (rho : (MulAut (Spin n F N))ᵐᵒᵖ →* M)
    (e : FieldGroup f) (g : SpecialClifford n F) :
    rho (spinInverseField fs e) * rho (spinInverseConjugation N g) =
      rho (spinInverseConjugation N (fs.action e g)) * rho (spinInverseField fs e) := by
  rw [← map_mul, spinInverseField_conjugation, map_mul]

/-- Actual inverse-field action on exact K0, over either coefficient field. -/
def spinFieldKZeroAction : Representation ℤ (FieldGroup f) (FDRepKZero k (Spin n F N)) :=
  (twistKZeroRepresentation (k := k) (G := Spin n F N)).comp (spinInverseField fs)

@[simp] theorem spinFieldKZeroAction_apply (e : FieldGroup f)
    (x : FDRepKZero k (Spin n F N)) :
    spinFieldKZeroAction (k := k) fs e x =
      twistKZero (k := k) (spinFieldAction n F fs e⁻¹) x := rfl

theorem spinFieldKZeroAction_intertwines (e : FieldGroup f) (g : SpecialClifford n F) :
    spinFieldKZeroAction (k := k) fs e * spinKZeroAction (k := k) N g =
      spinKZeroAction (k := k) N (fs.action e g) * spinFieldKZeroAction (k := k) fs e :=
  spinField_map_covariant fs (twistKZeroRepresentation (k := k) (G := Spin n F N)) e g

theorem spinFieldKZeroAction_covariant (e : FieldGroup f) (g : SpecialClifford n F)
    (x : FDRepKZero k (Spin n F N)) :
    spinFieldKZeroAction (k := k) fs e (spinKZeroAction (k := k) N g x) =
      spinKZeroAction (k := k) N (fs.action e g) (spinFieldKZeroAction (k := k) fs e x) :=
  congrArg (fun T : Module.End ℤ (FDRepKZero k (Spin n F N)) => T x)
    (spinFieldKZeroAction_intertwines (k := k) fs e g)

theorem spinFieldKZeroAction_conjugate (e : FieldGroup f) (g : SpecialClifford n F)
    (x : FDRepKZero k (Spin n F N)) :
    spinFieldKZeroAction (k := k) fs e
      (spinKZeroAction (k := k) N g (spinFieldKZeroAction (k := k) fs e⁻¹ x)) =
        spinKZeroAction (k := k) N (fs.action e g) x := by
  rw [spinFieldKZeroAction_covariant, Representation.self_inv_apply]

/-- Actual inverse-field permutation of primitive central idempotents. -/
def spinFieldBlockHom : FieldGroup f →* Equiv.Perm (LiteralPrimitiveBlock k (Spin n F N)) :=
  (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ
    (LiteralPrimitiveBlock k (Spin n F N))).comp (spinInverseField fs)

@[simp] theorem spinFieldBlockHom_apply (e : FieldGroup f)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinFieldBlockHom (k := k) fs e b =
      LiteralPrimitiveBlock.rightTwistBlock b (spinFieldAction n F fs e⁻¹) := rfl

theorem spinFieldBlockHom_intertwines (e : FieldGroup f) (g : SpecialClifford n F) :
    spinFieldBlockHom (k := k) fs e * spinBlockHom (k := k) N g =
      spinBlockHom (k := k) N (fs.action e g) * spinFieldBlockHom (k := k) fs e :=
  spinField_map_covariant fs
    (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ
      (LiteralPrimitiveBlock k (Spin n F N))) e g

theorem spinFieldBlockHom_covariant (e : FieldGroup f) (g : SpecialClifford n F)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinFieldBlockHom (k := k) fs e (spinBlockHom (k := k) N g b) =
      spinBlockHom (k := k) N (fs.action e g) (spinFieldBlockHom (k := k) fs e b) :=
  congrArg (fun T : Equiv.Perm (LiteralPrimitiveBlock k (Spin n F N)) => T b)
    (spinFieldBlockHom_intertwines (k := k) fs e g)

theorem spinFieldBlockHom_conjugate (e : FieldGroup f) (g : SpecialClifford n F)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinFieldBlockHom (k := k) fs e
      (spinBlockHom (k := k) N g (spinFieldBlockHom (k := k) fs e⁻¹ b)) =
        spinBlockHom (k := k) N (fs.action e g) b := by
  rw [spinFieldBlockHom_covariant, map_inv]
  exact congrArg (spinBlockHom (k := k) N (fs.action e g))
    ((spinFieldBlockHom (k := k) fs e).apply_symm_apply b)

section Ordinary

variable [CharZero k]

/-- Reuse the existing opposite pullback action on actual ordinary Irr. -/
def spinFieldOrdinaryHom :
    FieldGroup f →* Equiv.Perm (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) := by
  letI : MulAction (MulAut (Spin n F N))ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :=
    OddGFactorizationLemma312Relative.OrdinaryAction.oppositeAutomorphismAction
  exact (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ
    (OrdinaryIrreducibleCharacter.Irr k (Spin n F N))).comp (spinInverseField fs)

@[simp] theorem spinFieldOrdinaryHom_apply (e : FieldGroup f)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    spinFieldOrdinaryHom (k := k) fs e chi =
      OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
        (spinFieldAction n F fs e⁻¹) := rfl

theorem spinFieldOrdinaryHom_intertwines (e : FieldGroup f) (g : SpecialClifford n F) :
    spinFieldOrdinaryHom (k := k) fs e * spinOrdinaryHom (k := k) N g =
      spinOrdinaryHom (k := k) N (fs.action e g) * spinFieldOrdinaryHom (k := k) fs e := by
  letI : MulAction (MulAut (Spin n F N))ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :=
    OddGFactorizationLemma312Relative.OrdinaryAction.oppositeAutomorphismAction
  exact spinField_map_covariant fs
    (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr k (Spin n F N))) e g

theorem spinFieldOrdinaryHom_covariant (e : FieldGroup f) (g : SpecialClifford n F)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    spinFieldOrdinaryHom (k := k) fs e (spinOrdinaryHom (k := k) N g chi) =
      spinOrdinaryHom (k := k) N (fs.action e g) (spinFieldOrdinaryHom (k := k) fs e chi) :=
  congrArg (fun T : Equiv.Perm (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) => T chi)
    (spinFieldOrdinaryHom_intertwines (k := k) fs e g)

theorem spinFieldOrdinaryHom_conjugate (e : FieldGroup f) (g : SpecialClifford n F)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    spinFieldOrdinaryHom (k := k) fs e
      (spinOrdinaryHom (k := k) N g (spinFieldOrdinaryHom (k := k) fs e⁻¹ chi)) =
        spinOrdinaryHom (k := k) N (fs.action e g) chi := by
  rw [spinFieldOrdinaryHom_covariant, map_inv]
  exact congrArg (spinOrdinaryHom (k := k) N (fs.action e g))
    ((spinFieldOrdinaryHom (k := k) fs e).apply_symm_apply chi)

end Ordinary

section Brauer

variable {ell : ℕ} {K : Type u} [Field K] [CharZero K]
  [CharP k ell] [IsAlgClosed k] [Finite (Spin n F N)]
  (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- Actual prescribed-root Brauer field action; no character fixedness is assumed. -/
def spinFieldBrauerHom : FieldGroup f →* Equiv.Perm (IBr iota) :=
  (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ (IBr iota)).comp (spinInverseField fs)

@[simp] theorem spinFieldBrauerHom_apply (e : FieldGroup f) (phi : IBr iota) :
    spinFieldBrauerHom fs iota e phi =
      IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F fs e⁻¹) := rfl

theorem spinFieldBrauerHom_intertwines (e : FieldGroup f) (g : SpecialClifford n F) :
    spinFieldBrauerHom fs iota e * spinBrauerHom N iota g =
      spinBrauerHom N iota (fs.action e g) * spinFieldBrauerHom fs iota e :=
  spinField_map_covariant fs
    (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ (IBr iota)) e g

theorem spinFieldBrauerHom_covariant (e : FieldGroup f) (g : SpecialClifford n F)
    (phi : IBr iota) :
    spinFieldBrauerHom fs iota e (spinBrauerHom N iota g phi) =
      spinBrauerHom N iota (fs.action e g) (spinFieldBrauerHom fs iota e phi) :=
  congrArg (fun T : Equiv.Perm (IBr iota) => T phi)
    (spinFieldBrauerHom_intertwines fs iota e g)

theorem spinFieldBrauerHom_conjugate (e : FieldGroup f) (g : SpecialClifford n F)
    (phi : IBr iota) :
    spinFieldBrauerHom fs iota e
      (spinBrauerHom N iota g (spinFieldBrauerHom fs iota e⁻¹ phi)) =
        spinBrauerHom N iota (fs.action e g) phi := by
  rw [spinFieldBrauerHom_covariant, map_inv]
  exact congrArg (spinBrauerHom N iota (fs.action e g))
    ((spinFieldBrauerHom fs iota e).apply_symm_apply phi)

end Brauer

end ModularRep.PaperProofs.TypeBSpinFieldClassActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
