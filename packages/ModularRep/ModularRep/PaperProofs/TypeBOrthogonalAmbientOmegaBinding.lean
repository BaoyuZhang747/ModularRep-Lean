import ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientActionBinding

/-!
# The literal matrix Omega inside the SO/field ambient

The embedding is the actual Omega-to-SO inclusion followed by the left
semidirect inclusion. Its image is normal because the already constructed
SO/field action has exactly the ambient conjugation formula. The resulting
group equivalence identifies that same action with `originalAction` on the
embedded subgroup, for every SO and field coordinate.

No new source field, centre assertion or full-automorphism assertion is
introduced. Finiteness uses the finite coordinate field and the positive
field exponent in the existing odd-field parameters.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBOrthogonalAmbientOmegaBinding

open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBCliffordOrthogonalSourceBinding TypeBCliffordOrthogonalAmbientQuotient
open TypeBCliffordOrthogonalAmbientActionBinding TypeBCentralKernelCarriers

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (S : FieldActionSource n F p f parameters N) (rank : 3 ≤ n)
  (C : Source n F p f parameters rank N)

/-- The source and target are the already fixed matrix Omega and actual
SO/field semidirect product. -/
def omegaEmbedding : Omega n F →* OrthogonalAmbient n F parameters rank N C S :=
  SemidirectProduct.inl.comp (omegaSubgroup n F).subtype

@[simp] theorem omegaEmbedding_left (x : Omega n F) :
    (omegaEmbedding S rank C x).left = x.val := rfl

@[simp] theorem omegaEmbedding_right (x : Omega n F) :
    (omegaEmbedding S rank C x).right = 1 := rfl

theorem omegaEmbedding_injective : Function.Injective (omegaEmbedding S rank C) :=
  SemidirectProduct.inl_injective.comp Subtype.val_injective

/-- The characteristic-subgroup action already constructed on matrix
Omega agrees pointwise with conjugation in this very semidirect product. -/
theorem omegaEmbedding_action
    (a : OrthogonalAmbient n F parameters rank N C S) (x : Omega n F) :
    omegaEmbedding S rank C (omegaAmbientAction S rank C a x) =
      a * omegaEmbedding S rank C x * a⁻¹ := by
  apply SemidirectProduct.ext
  · change omegaToSpecialOrthogonal n F (omegaAmbientAction S rank C a x) = _
    rw [omegaAmbientAction_value]
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      omegaEmbedding_left, omegaEmbedding_right, SemidirectProduct.inv_left,
      mul_one, map_inv, MulAut.apply_inv_self]
  · simp only [SemidirectProduct.mul_right, omegaEmbedding_right,
      SemidirectProduct.inv_right, mul_one, mul_inv_cancel]

/-- The embedded base group is the actual range of the displayed map. -/
def embeddedOmega : Subgroup (OrthogonalAmbient n F parameters rank N C S) :=
  (omegaEmbedding S rank C).range

@[simp] theorem mem_embeddedOmega
    (a : OrthogonalAmbient n F parameters rank N C S) :
    a ∈ embeddedOmega S rank C ↔ a.right = 1 ∧ a.left ∈ omegaSubgroup n F := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨rfl, x.property⟩
  · intro ha
    refine ⟨⟨a.left, ha.2⟩, ?_⟩
    exact SemidirectProduct.ext rfl ha.1.symm

instance embeddedOmega_normal : (embeddedOmega S rank C).Normal where
  conj_mem _ hx a := by
    obtain ⟨x, rfl⟩ := hx
    exact ⟨omegaAmbientAction S rank C a x, omegaEmbedding_action S rank C a x⟩

/-- The canonical equivalence to the literal ambient image has the
displayed embedding as its value map. -/
def omegaEquiv : Omega n F ≃* embeddedOmega S rank C :=
  MonoidHom.ofInjective (omegaEmbedding_injective S rank C)

@[simp] theorem omegaEquiv_val (x : Omega n F) :
    (omegaEquiv S rank C x : OrthogonalAmbient n F parameters rank N C S) =
      omegaEmbedding S rank C x := rfl

@[simp] theorem omegaEmbedding_equiv_symm (x : embeddedOmega S rank C) :
    omegaEmbedding S rank C ((omegaEquiv S rank C).symm x) = x.val :=
  MonoidHom.apply_ofInjective_symm (omegaEmbedding_injective S rank C) x

/-- The exact action square needed to instantiate the actual inertia and
triple constructions with this embedded matrix group. -/
theorem omegaEquiv_action
    (a : OrthogonalAmbient n F parameters rank N C S) (x : Omega n F) :
    omegaEquiv S rank C (omegaAmbientAction S rank C a x) =
      originalAction (embeddedOmega S rank C) a (omegaEquiv S rank C x) := by
  apply Subtype.ext
  exact omegaEmbedding_action S rank C a x

theorem omegaEquiv_symm_action
    (a : OrthogonalAmbient n F parameters rank N C S) (x : embeddedOmega S rank C) :
    (omegaEquiv S rank C).symm (originalAction (embeddedOmega S rank C) a x) =
      omegaAmbientAction S rank C a ((omegaEquiv S rank C).symm x) := by
  apply (omegaEquiv S rank C).injective
  rw [MulEquiv.apply_symm_apply, omegaEquiv_action, MulEquiv.apply_symm_apply]

/-- Equality of the actual homomorphisms into the same embedded-group
automorphism carrier; this does not assert that their image is full Aut. -/
theorem omegaEquiv_intertwines :
    (MulAut.congr (omegaEquiv S rank C)).toMonoidHom.comp
        (omegaAmbientAction S rank C) =
      originalAction (embeddedOmega S rank C) := by
  apply MonoidHom.ext
  intro a
  apply MulEquiv.ext
  intro x
  change omegaEquiv S rank C
      (omegaAmbientAction S rank C a ((omegaEquiv S rank C).symm x)) = _
  rw [omegaEquiv_action]
  exact congrArg (originalAction (embeddedOmega S rank C) a)
    ((omegaEquiv S rank C).apply_symm_apply x)

/-- The ambient is finite on these same parameters. The field actor is
`Multiplicative (ZMod f)` with f positive, not an arbitrary finite group. -/
instance orthogonalAmbient_finite :
    Finite (OrthogonalAmbient n F parameters rank N C S) := by
  letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
  exact Finite.of_injective
    (SemidirectProduct.equivProd : OrthogonalAmbient n F parameters rank N C S ≃
      SpecialOrthogonal n F × FieldGroup f)
    SemidirectProduct.equivProd.injective

end ModularRep.PaperProofs.TypeBOrthogonalAmbientOmegaBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
