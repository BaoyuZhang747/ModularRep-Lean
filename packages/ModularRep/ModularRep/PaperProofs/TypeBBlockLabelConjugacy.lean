import ModularRep.PaperProofs.TypeBConlonBlockRelative
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The block-label join in Type B Lemma 4.2

FLZ (2022), Theorem 6.3(1), classifies blocks by conjugacy orbits of
semisimple/core pairs. Part (2), at the commuting ell-element t = 1,
identifies the block of a character label with its core pair. Lemma 3.6
describes tensor translation of the character label. This file derives the
same-block conjugacy implication from these separate inputs; it is not an
input. The scalar restriction and field projection are constructed as well.

The label carriers in this reusable join remain parameters. A source
application must bind them to the literal FLZ pairs, core operation and
character parametrisation. No arbitrary label carrier is certified here.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBBlockLabelConjugacy

universe u

variable {X Block Dual CharacterLabel BlockLabel : Type u}
variable [Group Dual] [MulAction Dual BlockLabel]

/-- The two separately published parts of FLZ Theorem 6.3, together with
the first-coordinate map on conjugate core pairs. The application uses
literal ordinary characters for `X` and primitive modular idempotents for
`Block`. This certificate has no Brauer-character or set-bijection target.
-/
structure BlockLabelSource (ordinaryBlock : X → Block) where
  character : CharacterLabel → X
  character_surjective : Function.Surjective character
  characterParameter : CharacterLabel → Dual
  core : CharacterLabel → BlockLabel
  blockParameter : BlockLabel → Dual
  core_parameter : ∀ l, blockParameter (core l) = characterParameter l
  parameter_conjugation : ∀ (g : Dual) (b : BlockLabel),
    blockParameter (g • b) = g * blockParameter b * g⁻¹
  classification : MulAction.orbitRel.Quotient Dual BlockLabel ≃ Block
  membership : ∀ l,
    ordinaryBlock (character l) = classification (Quotient.mk _ (core l))

namespace BlockLabelSource

variable {ordinaryBlock : X → Block}
variable (S : BlockLabelSource (Dual := Dual) (CharacterLabel := CharacterLabel)
  (BlockLabel := BlockLabel) ordinaryBlock)

/-- Equality of the actual block forces conjugacy of the semisimple
parameters, by injectivity of the published orbit classification. -/
theorem parameters_isConj_of_same_block (l m : CharacterLabel)
    (h : ordinaryBlock (S.character l) = ordinaryBlock (S.character m)) :
    IsConj (S.characterParameter l) (S.characterParameter m) := by
  rw [S.membership, S.membership] at h
  have horbit := Quotient.exact (S.classification.injective h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
  have hp : S.characterParameter l = g * S.characterParameter m * g⁻¹ := by
    rw [← S.core_parameter l, ← hg, S.parameter_conjugation, S.core_parameter]
  exact (isConj_iff.mpr ⟨g, hp.symm⟩).symm

end BlockLabelSource

section FieldProjection

variable {C E : Type u} [Group C] [Group E]
variable (action : E →* MulAut C)

/-- The actual second-coordinate projection restricted to a subgroup. -/
def fieldProjection (J : Subgroup (C ⋊[action] E)) : J →* E :=
  SemidirectProduct.rightHom.comp J.subtype

/-- The manuscript intersection `J ∩ C` is the kernel of this projection. -/
theorem fieldProjection_ker (J : Subgroup (C ⋊[action] E)) :
    (fieldProjection action J).ker =
      (SemidirectProduct.inl : C →* C ⋊[action] E).range.comap J.subtype := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  rfl

/-- First coordinate on the exact tensor kernel. -/
def kernelTensor (J : Subgroup (C ⋊[action] E))
    (d : (fieldProjection action J).ker) : C := d.1.1.left

theorem kernel_right_eq_one (J : Subgroup (C ⋊[action] E))
    (d : (fieldProjection action J).ker) : d.1.1.right = 1 := d.2

theorem kernel_eq_inl (J : Subgroup (C ⋊[action] E))
    (d : (fieldProjection action J).ker) :
    d.1.1 = SemidirectProduct.inl (kernelTensor action J d) := by
  ext
  · rfl
  · exact kernel_right_eq_one action J d

theorem kernelTensor_injective (J : Subgroup (C ⋊[action] E)) :
    Function.Injective (kernelTensor action J) := by
  intro d e h
  apply Subtype.ext
  apply Subtype.ext
  rw [kernel_eq_inl action J d, kernel_eq_inl action J e, h]

variable {F : Type u} [Field F]

/-- The inverse scalar is required by the existing left-action realization
of the manuscript's right tensor action. -/
def kernelScalar (J : Subgroup (C ⋊[action] E)) (scalar : C → Fˣ)
    (d : (fieldProjection action J).ker) : Fˣ :=
  (scalar (kernelTensor action J d))⁻¹

theorem kernelScalar_injective (J : Subgroup (C ⋊[action] E))
    (scalar : C → Fˣ) (hinj : Function.Injective scalar) :
    Function.Injective (kernelScalar action J scalar) := by
  intro d e h
  apply kernelTensor_injective action J
  apply hinj
  exact inv_injective h

variable [MulAction (C ⋊[action] E) X]
variable [MulAction (C ⋊[action] E) Block]

/-- Tensor-label translation and the two parts of Theorem 6.3 imply the
translated-conjugacy input of the checked Conlon deduction. The witness is
an ordinary character label in the chosen block; it is obtained from basic
set nonemptiness in the application. -/
theorem translated_conjugate
    (ordinaryBlock : X → Block)
    (block_equivariant : ∀ (a : C ⋊[action] E) (x : X),
      ordinaryBlock (a • x) = a • ordinaryBlock x)
    (S : BlockLabelSource (Dual := Dual) (CharacterLabel := CharacterLabel)
      (BlockLabel := BlockLabel) ordinaryBlock)
    (scalar : C → Fˣ) (centralScalar : Fˣ →* Dual)
    (tensorLabel : C → CharacterLabel → CharacterLabel)
    (tensor_character : ∀ c l,
      S.character (tensorLabel c l) =
        (SemidirectProduct.inl c : C ⋊[action] E) • S.character l)
    (tensor_parameter : ∀ c l,
      S.characterParameter (tensorLabel c l) =
        centralScalar (scalar c)⁻¹ * S.characterParameter l)
    (b : Block) (l : CharacterLabel) (hl : ordinaryBlock (S.character l) = b) :
    ∀ d : (fieldProjection action (MulAction.stabilizer (C ⋊[action] E) b)).ker,
      IsConj (S.characterParameter l)
        (centralScalar
          (kernelScalar action (MulAction.stabilizer (C ⋊[action] E) b) scalar d) *
            S.characterParameter l) := by
  intro d
  let c := kernelTensor action (MulAction.stabilizer (C ⋊[action] E) b) d
  have hb : ordinaryBlock (S.character (tensorLabel c l)) = b := by
    rw [tensor_character, block_equivariant, hl]
    rw [← kernel_eq_inl action (MulAction.stabilizer (C ⋊[action] E) b) d]
    exact d.1.2
  have hc := S.parameters_isConj_of_same_block l (tensorLabel c l) (hl.trans hb.symm)
  simpa only [tensor_parameter, kernelScalar, map_inv, c] using hc

end FieldProjection

end ModularRep.PaperProofs.TypeBBlockLabelConjugacy


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
