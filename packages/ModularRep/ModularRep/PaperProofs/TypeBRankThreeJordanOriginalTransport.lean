import ModularRep.PaperProofs.TypeBLeviRepresentativeOriginalExtension
import ModularRep.PaperProofs.TypeBLeviRepresentativeSelection
import ModularRep.StabilizerFactorizationTransport

/-!
# Original Levi actions for the same selected representative

The original rational L and its subgroup copy H inside Gamma have the
existing canonical group and root equivalences. This module transports
the literal Gamma conjugation back to original L, proves its point values,
and uses the same FieldData for the original finite field actor. Both
character-action squares and semidirect compatibility are deductions.

The preceding factorization on the copied character gives the original
character's factorization. The field-fixer equality is reused from the
accepted original-extension transport. No new source, Jordan map, actor
quotient, character choice, or character compatibility is supplied here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeJordanOriginalTransport

open TypeBRegularLeviRationalCarriers TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLemma47LeviApplication
open EvenFieldAssumption53Relative
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {A E k K : Type} [Group A] [Group E]
variable (Frob : MulAut A) (Lbar : Subgroup A)

/-- Conjugation on original L, through its canonical normal subgroup copy. -/
def originalConjugation :
    Gamma Frob Lbar →* MulAut (L Frob.toMonoidHom Lbar) :=
  (MulAut.congr (originalLEquiv Frob Lbar).symm).toMonoidHom.comp
    (MulAut.conjNormal (H := H Frob Lbar))

@[simp] theorem originalConjugation_value
    (g : Gamma Frob Lbar) (x : L Frob.toMonoidHom Lbar) :
    (originalConjugation Frob Lbar g x).val =
      g.val * x.val * g.val⁻¹ := rfl

/-- The original and copied automorphisms have the same literal values. -/
theorem originalLEquiv_conjugation_square (g : Gamma Frob Lbar) :
    MulAut.congr (originalLEquiv Frob Lbar) (originalConjugation Frob Lbar g) =
      MulAut.conjNormal (H := H Frob Lbar) g := by
  ext x
  rfl

/-- Returning to original L leaves the conjugation kernel unchanged. -/
theorem originalConjugation_kernel :
    (originalConjugation Frob Lbar).ker =
      (MulAut.conjNormal (H := H Frob Lbar)).ker := by
  ext g
  change MulAut.congr (originalLEquiv Frob Lbar).symm
      (MulAut.conjNormal (H := H Frob Lbar) g) = 1 ↔
    MulAut.conjNormal (H := H Frob Lbar) g = 1
  exact (MulAut.congr (originalLEquiv Frob Lbar).symm).map_eq_one_iff

variable [Finite (fixedPoints Frob.toMonoidHom)]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (root : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))

abbrev characterEquiv : IBr root ≃ IBr (rootH Frob Lbar root) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar)

/-- The literal inverse-pullback Gamma action on the original root. -/
@[instance_reducible]
def originalAmbientAction : MulAction (Gamma Frob Lbar) (IBr root) :=
  rightAutomorphismAction root (originalConjugation Frob Lbar)

theorem characterEquiv_ambient (g : Gamma Frob Lbar) (psi : IBr root) :
    letI := originalAmbientAction Frob Lbar root
    letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
    characterEquiv Frob Lbar root (g • psi) =
      g • characterEquiv Frob Lbar root psi := by
  change IrreducibleBrauerCharacter.equivAlongMulEquiv root (originalLEquiv Frob Lbar)
      (IrreducibleBrauerCharacter.twist root psi
        (originalConjugation Frob Lbar g⁻¹)) =
    IrreducibleBrauerCharacter.twist (rootH Frob Lbar root)
      (characterEquiv Frob Lbar root psi)
      (MulAut.conjNormal (H := H Frob Lbar) g⁻¹)
  rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist,
    originalLEquiv_conjugation_square]
  rfl

variable (field : FieldData Frob Lbar E)

/-- The same finite point actor restricted directly to original L. -/
abbrev originalField : E →* MulAut (L Frob.toMonoidHom Lbar) :=
  TypeBLeviRepresentativeOriginalExtension.fieldOnOriginalL Frob Lbar field.sigma
    field.injective field.commutes field.sigma_levi field.sigma_centre
    field.fieldPoints field.generator field.generates field.generatorValue

@[instance_reducible]
def originalFieldAction : MulAction E (IBr root) :=
  rightAutomorphismAction root (originalField Frob Lbar field)

/-- Field equivariance is the existing original-root transport for this
same FieldData; no new action square is an input. -/
theorem characterEquiv_field (e : E) (psi : IBr root) :
    letI := originalFieldAction Frob Lbar root field
    letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
      field.fieldOnGamma field.H_stable
    characterEquiv Frob Lbar root (e • psi) =
      e • characterEquiv Frob Lbar root psi :=
  TypeBLeviRepresentativeOriginalExtension.original_character_field_transport
    Frob Lbar field.sigma field.injective field.commutes field.sigma_levi
    field.sigma_centre field.fieldPoints field.generator field.generates
    field.generatorValue root psi e

/-- Compatibility follows by injective transport to the already compatible
literal actions on the copied root. -/
theorem original_semidirect_compatible :
    letI := originalAmbientAction Frob Lbar root
    letI := originalFieldAction Frob Lbar root field
    Formalisation.SemidirectActionCompatible (X := IBr root) field.fieldOnGamma := by
  letI := originalAmbientAction Frob Lbar root
  letI := originalFieldAction Frob Lbar root field
  letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
  letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
    field.fieldOnGamma field.H_stable
  intro e g psi
  apply (characterEquiv Frob Lbar root).injective
  rw [characterEquiv_field, characterEquiv_ambient,
    characterEquiv_ambient, characterEquiv_field]
  exact field_ambient_brauer_naturality (H Frob Lbar) (rootH Frob Lbar root)
    field.fieldOnGamma field.H_stable e g (characterEquiv Frob Lbar root psi)

/-- The selected copied character is returned canonically, then its
preceding factorization is transported through the existing equivalence. -/
theorem original_product_factorization
    (psiH : IBr (rootH Frob Lbar root))
    (copy_factorization :
      letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
      letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
        field.fieldOnGamma field.H_stable
      Formalisation.SemidirectStabilizerFactors field.fieldOnGamma
        (field_ambient_semidirect_compatible (H Frob Lbar) (rootH Frob Lbar root)
          field.fieldOnGamma field.H_stable) psiH) :
    letI := originalAmbientAction Frob Lbar root
    letI := originalFieldAction Frob Lbar root field
    ProductStabilizerFactorization (D := Gamma Frob Lbar) (E := E)
      (TypeBLeviRepresentativeOriginalExtension.originalCharacter Frob Lbar root psiH) := by
  letI := originalAmbientAction Frob Lbar root
  letI := originalFieldAction Frob Lbar root field
  letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
  letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
    field.fieldOnGamma field.H_stable
  apply (productStabilizerFactorization_iff_of_equivariantEquiv
    (characterEquiv Frob Lbar root)
    (characterEquiv_ambient Frob Lbar root)
    (characterEquiv_field Frob Lbar root field)
    (TypeBLeviRepresentativeOriginalExtension.originalCharacter Frob Lbar root psiH)).mpr
  have copied := (semidirectStabilizerFactors_iff_productStabilizerFactorization
    field.fieldOnGamma
    (field_ambient_semidirect_compatible (H Frob Lbar) (rootH Frob Lbar root)
      field.fieldOnGamma field.H_stable) psiH).mp copy_factorization
  have transport : characterEquiv Frob Lbar root
      (TypeBLeviRepresentativeOriginalExtension.originalCharacter Frob Lbar root psiH) =
        psiH :=
    TypeBLeviRepresentativeOriginalExtension.originalCharacter_transport
      Frob Lbar root psiH
  rw [transport]
  exact copied

/-- The factorization on original L uses the unchanged Gamma semidirect E. -/
theorem original_semidirect_factorization
    (psiH : IBr (rootH Frob Lbar root))
    (copy_factorization :
      letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
      letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar root)
        field.fieldOnGamma field.H_stable
      Formalisation.SemidirectStabilizerFactors field.fieldOnGamma
        (field_ambient_semidirect_compatible (H Frob Lbar) (rootH Frob Lbar root)
          field.fieldOnGamma field.H_stable) psiH) :
    letI := originalAmbientAction Frob Lbar root
    letI := originalFieldAction Frob Lbar root field
    Formalisation.SemidirectStabilizerFactors field.fieldOnGamma
      (original_semidirect_compatible Frob Lbar root field)
      (TypeBLeviRepresentativeOriginalExtension.originalCharacter Frob Lbar root psiH) := by
  letI := originalAmbientAction Frob Lbar root
  letI := originalFieldAction Frob Lbar root field
  apply (semidirectStabilizerFactors_iff_productStabilizerFactorization
    field.fieldOnGamma (original_semidirect_compatible Frob Lbar root field) _).mpr
  exact original_product_factorization Frob Lbar root field psiH copy_factorization

/-- Reuse the existing equality in the original actor E, without replacing
that actor by an effective image or quotient. -/
theorem original_field_fixer_eq (psiH : IBr (rootH Frob Lbar root)) :
    TypeBLeviRepresentativeField.fieldStabilizer root (originalField Frob Lbar field)
        (TypeBLeviRepresentativeOriginalExtension.originalCharacter Frob Lbar root psiH) =
      TypeBLeviRepresentativeField.fieldStabilizer (rootH Frob Lbar root)
        (restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable) psiH :=
  TypeBLeviRepresentativeOriginalExtension.original_field_stabilizer_eq
    Frob Lbar field.sigma field.injective field.commutes field.sigma_levi
    field.sigma_centre field.fieldPoints field.generator field.generates
    field.generatorValue root psiH

end ModularRep.PaperProofs.TypeBRankThreeJordanOriginalTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
