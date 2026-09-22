import ModularRep.PaperProofs.TypeBLeviRepresentativeCarriers
import ModularRep.PaperProofs.TypeBLeviRepresentativeField

/-!
# The honest field extension on the original rational Levi

The final representative must be a character of the ORIGINAL rational L,
with its prescribed original root embedding. The subgroup copy H inside
Gamma is used only to import the character already selected by the preceding
deduction. Its inverse character transport is the canonical equivalence
induced by Carriers.originalLEquiv; no new choice of a character is made.

The field action on original L is the restriction of the SAME fieldPoints.
Its preservation is derived from the supplied point endomorphism and the
same finite cyclic generator, using the checked carrier theorem. It agrees
under originalLEquiv with the H action used by the preceding deduction, so
the two field fixers are the SAME subgroup of the original actor E.

Finally TypeBLeviRepresentativeField.honest_field_extension is applied directly on original L.
The output is an irreducible representation on the literal semidirect group
L semidirect E_psi, with an exact original-root character equation and a
representation equivalence for restriction along its actual inl. The only
representation theoretic source remains the same uniform Navarro 8.12
principle. No target extension, new selector, or root agreement is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeOriginalExtension

open TypeBRegularLeviRationalCarriers TypeBLemma47LeviApplication
open TypeBLeviRepresentativeCarriers EvenFieldAssumption53Relative

universe u

variable {A E k K : Type u} [Group A] [Group E]
variable (Frob : MulAut A) (Lbar : Subgroup A)
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable (sigma : A →* A) (injective : Function.Injective sigma)
variable (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
variable (sigma_levi : ∀ x ∈ Lbar, sigma x ∈ Lbar)
variable (sigma_centre : ∀ z ∈ Subgroup.center A, sigma z ∈ Subgroup.center A)
variable (fieldPoints : E →* MulAut (fixedPoints Frob.toMonoidHom))
variable (generator : E) (generates : Subgroup.zpowers generator = ⊤)
variable (generatorValue : ∀ x : fixedPoints Frob.toMonoidHom,
  fieldPoints generator x = TypeBRegularLeviCurrentQuotient.fixedPointAutomorphism
    Frob.toMonoidHom sigma commutes injective x)

/-- Restrict the original finite field actor directly to original L. -/
def fieldOnOriginalL : E →* MulAut (L Frob.toMonoidHom Lbar) :=
  restrictAutomorphismHom (L Frob.toMonoidHom Lbar) fieldPoints (fun a x =>
    mem_iff_of_map_eq (L Frob.toMonoidHom Lbar) (fieldPoints a)
      (fieldPoints_preserves_chain Frob Lbar sigma injective commutes sigma_levi
        sigma_centre fieldPoints generator generates generatorValue a).2.1 x)

/-- The already used field action on the literal copy H inside Gamma. -/
def fieldOnCopyL : E →* MulAut (H Frob Lbar) :=
  restrictAutomorphismHom (H Frob Lbar)
    (fieldOnGamma Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints generator generates generatorValue)
    (fieldOnGamma_H_stable Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints generator generates generatorValue)

@[simp] theorem fieldOnOriginalL_value (a : E) (x : L Frob.toMonoidHom Lbar) :
    (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints generator generates generatorValue a x).val = fieldPoints a x.val := rfl

/-- Both actions come from the same fieldPoints value, through the original
subgroup equivalence. No character-action square is a source input. -/
theorem originalLEquiv_field_square (a : E) :
    MulAut.congr (originalLEquiv Frob Lbar)
        (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
          fieldPoints generator generates generatorValue a) =
      fieldOnCopyL Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints generator generates generatorValue a := by
  ext x
  rfl

variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The selected H character returned to the prescribed original root. -/
def originalCharacter
    (root : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
    (psiH : IBr (rootH Frob Lbar root)) : IBr root :=
  (IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar)).symm psiH

@[simp] theorem originalCharacter_transport
    (root : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
    (psiH : IBr (rootH Frob Lbar root)) :
    IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar)
      (originalCharacter Frob Lbar root psiH) = psiH :=
  Equiv.apply_symm_apply _ psiH

@[simp] theorem originalCharacter_value
    (root : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
    (psiH : IBr (rootH Frob Lbar root))
    (x : PrimeRegularElement (G := L Frob.toMonoidHom Lbar) 2) :
    (originalCharacter Frob Lbar root psiH).1 x =
      psiH.1 (PrimeRegularElement.map (originalLEquiv Frob Lbar).toMonoidHom x) := rfl

/-- Canonical character transport intertwines the same finite field actor
on original L and its subgroup copy. -/
theorem original_character_field_transport
    (root : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
    (psi : IBr root) (a : E) :
    letI := rightAutomorphismAction root
      (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints generator generates generatorValue)
    letI := rightAutomorphismAction (rootH Frob Lbar root)
      (fieldOnCopyL Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints generator generates generatorValue)
    IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar) (a • psi) =
      a • (show IBr (rootH Frob Lbar root) from
        IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar) psi) := by
  change IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar)
      (IrreducibleBrauerCharacter.twist root psi
        (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
          fieldPoints generator generates generatorValue a⁻¹)) =
    IrreducibleBrauerCharacter.twist (rootH Frob Lbar root)
      (IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar) psi)
      (fieldOnCopyL Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints generator generates generatorValue a⁻¹)
  rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist,
    originalLEquiv_field_square]
  rfl

/-- The original and copied field fixers are literally equal subgroups of E. -/
theorem original_field_stabilizer_eq
    (root : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
    (psiH : IBr (rootH Frob Lbar root)) :
    TypeBLeviRepresentativeField.fieldStabilizer root
        (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
          fieldPoints generator generates generatorValue)
        (originalCharacter Frob Lbar root psiH) =
      TypeBLeviRepresentativeField.fieldStabilizer (rootH Frob Lbar root)
        (fieldOnCopyL Frob Lbar sigma injective commutes sigma_levi sigma_centre
          fieldPoints generator generates generatorValue) psiH := by
  letI := rightAutomorphismAction root
    (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints generator generates generatorValue)
  letI := rightAutomorphismAction (rootH Frob Lbar root)
    (fieldOnCopyL Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints generator generates generatorValue)
  let beta : IBr root ≃ IBr (rootH Frob Lbar root) :=
    IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar)
  ext a
  change a • originalCharacter Frob Lbar root psiH = originalCharacter Frob Lbar root psiH ↔
    a • psiH = psiH
  have htransport : beta (a • originalCharacter Frob Lbar root psiH) = a • psiH := by
    change IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar)
        (IrreducibleBrauerCharacter.twist root (originalCharacter Frob Lbar root psiH)
          (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
            fieldPoints generator generates generatorValue a⁻¹)) =
      IrreducibleBrauerCharacter.twist (root.alongMulEquiv (originalLEquiv Frob Lbar))
        psiH (fieldOnCopyL Frob Lbar sigma injective commutes sigma_levi sigma_centre
          fieldPoints generator generates generatorValue a⁻¹)
    rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist,
      originalLEquiv_field_square, originalCharacter_transport]
  constructor
  · intro h
    rw [← htransport, h]
    exact originalCharacter_transport Frob Lbar root psiH
  · intro h
    apply beta.injective
    rw [htransport, h]
    exact (originalCharacter_transport Frob Lbar root psiH).symm

/-- Extension of the selected character on ORIGINAL rational L,
with the original root, actual field fixer and literal semidirect inl. -/
theorem honest_original_field_extension [Finite E] [IsCyclic E]
    (root : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
    (psiH : IBr (rootH Frob Lbar root))
    (navarro : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k) :
    let phi := fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints generator generates generatorValue
    ∃ psi : IBr root,
      IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar) psi = psiH ∧
      TypeBLeviRepresentativeField.fieldStabilizer root phi psi =
        TypeBLeviRepresentativeField.fieldStabilizer (rootH Frob Lbar root)
          (fieldOnCopyL Frob Lbar sigma injective commutes sigma_levi sigma_centre
            fieldPoints generator generates generatorValue) psiH ∧
      ∃ W : FDRep k (L Frob.toMonoidHom Lbar),
        Representation.IsIrreducible W.ρ ∧
        psi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ root ∧
        ∃ rho : Representation k (TypeBLeviRepresentativeField.FieldSemidirect root phi psi) W,
          Representation.IsIrreducible rho ∧
          Nonempty (Representation.Equiv
            (rho.pullback (SemidirectProduct.inl :
              L Frob.toMonoidHom Lbar →*
                TypeBLeviRepresentativeField.FieldSemidirect root phi psi)) W.ρ) := by
  refine ⟨originalCharacter Frob Lbar root psiH,
    originalCharacter_transport Frob Lbar root psiH, ?_, ?_⟩
  · exact original_field_stabilizer_eq Frob Lbar sigma injective commutes sigma_levi
      sigma_centre fieldPoints generator generates generatorValue root psiH
  · exact TypeBLeviRepresentativeField.honest_field_extension root
      (fieldOnOriginalL Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints generator generates generatorValue) navarro
      (originalCharacter Frob Lbar root psiH)

end ModularRep.PaperProofs.TypeBLeviRepresentativeOriginalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
