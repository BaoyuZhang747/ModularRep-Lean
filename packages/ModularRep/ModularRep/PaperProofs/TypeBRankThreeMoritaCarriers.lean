import ModularRep.PaperProofs.TypeBRankThreeJordanCliffordCarriers
import ModularRep.PaperProofs.TypeBRankThreeJordanOriginalTransport

/-!
# The original Levi inclusion and the same field semidirect groups

The original rational Levi and finite Spin group are the accepted fixed-point
carriers. Their field actions come from the same finite point action. The
inclusion square below is derived from those point values, and supplies the
canonical inclusion of their semidirect products by any actual subgroup of E.

This is supporting carrier work for the induced Morita manuscript window.
No character, block, bimodule, Morita equivalence or extension is an input.
The field/finite-point interpretations retain their existing source scope.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaCarriers

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBLeviRepresentativeSelection TypeBRankThreeJordanCliffordCarriers
open TypeBRankThreeJordanOriginalTransport

variable {p f : ℕ} {F A E : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A] [Group E]
variable {N : NormSource 3 F} {Nbar : NormSource 3 A}
variable {Frob : MulAut (SpecialClifford 3 A)}
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
variable (Lbar : Subgroup (SpecialClifford 3 A))
variable (levi_le_spin : Lbar ≤ SpinSubgroup 3 A Nbar)
variable (field : FieldData Frob Lbar E)
variable (perfect : commutator (Spin 3 F N) = ⊤)

/-- The actual original Levi inclusion intertwines the same point field action. -/
theorem originalLSpinEmbedding_field (e : E) (x : L Frob.toMonoidHom Lbar) :
    originalLSpinEmbedding points Lbar levi_le_spin (originalField Frob Lbar field e x) =
      spinFieldAction points field.fieldPoints perfect e
        (originalLSpinEmbedding points Lbar levi_le_spin x) := by
  apply Subtype.ext
  apply (ambientEquiv points).injective
  change ambientEquiv points
      (originalLCliffordEmbedding points Lbar (originalField Frob Lbar field e x)) =
    ambientEquiv points
      (spinFieldAction points field.fieldPoints perfect e
        (originalLSpinEmbedding points Lbar levi_le_spin x)).val
  rw [originalLCliffordEmbedding_point, spinFieldAction_point]
  change field.fieldPoints e x.val =
    field.fieldPoints e (ambientEquiv points (originalLCliffordEmbedding points Lbar x))
  rw [originalLCliffordEmbedding_point]

/-- Same original Levi semidirect the literal subgroup of the chosen field actor. -/
abbrev LeviOvergroup (Q : Subgroup E) :=
  (L Frob.toMonoidHom Lbar) ⋊[(originalField Frob Lbar field).comp Q.subtype] Q

/-- Same finite Spin group semidirect that identical field subgroup. -/
abbrev SpinOvergroup (Q : Subgroup E) :=
  (Spin 3 F N) ⋊[(spinFieldAction points field.fieldPoints perfect).comp Q.subtype] Q

/-- The canonical semidirect inclusion is the original Levi inclusion on the
left and the identity of the original field subgroup on the right. -/
def originalSemidirectEmbedding (Q : Subgroup E) :
    LeviOvergroup Lbar field Q →* SpinOvergroup points Lbar field perfect Q :=
  SemidirectProduct.map (originalLSpinEmbedding points Lbar levi_le_spin)
    (MonoidHom.id Q) (fun e => by
      apply MonoidHom.ext
      intro x
      exact originalLSpinEmbedding_field points Lbar levi_le_spin field perfect e.val x)

@[simp] theorem originalSemidirectEmbedding_left (Q : Subgroup E)
    (x : LeviOvergroup Lbar field Q) :
    (originalSemidirectEmbedding points Lbar levi_le_spin field perfect Q x).left =
      originalLSpinEmbedding points Lbar levi_le_spin x.left := rfl

@[simp] theorem originalSemidirectEmbedding_right (Q : Subgroup E)
    (x : LeviOvergroup Lbar field Q) :
    (originalSemidirectEmbedding points Lbar levi_le_spin field perfect Q x).right =
      x.right := rfl

theorem originalSemidirectEmbedding_injective (Q : Subgroup E) :
    Function.Injective (originalSemidirectEmbedding points Lbar levi_le_spin field perfect Q) := by
  intro x y equal
  apply SemidirectProduct.ext
  · exact originalLSpinEmbedding_injective points Lbar levi_le_spin
      (congrArg SemidirectProduct.left equal)
  · exact congrArg (fun z : SpinOvergroup points Lbar field perfect Q => z.right) equal

@[simp] theorem originalSemidirectEmbedding_inl (Q : Subgroup E)
    (x : L Frob.toMonoidHom Lbar) :
    originalSemidirectEmbedding points Lbar levi_le_spin field perfect Q
        (SemidirectProduct.inl x) =
      SemidirectProduct.inl (originalLSpinEmbedding points Lbar levi_le_spin x) := by
  simp only [originalSemidirectEmbedding, SemidirectProduct.map_inl]

@[simp] theorem originalSemidirectEmbedding_inr (Q : Subgroup E) (e : Q) :
    originalSemidirectEmbedding points Lbar levi_le_spin field perfect Q
        (SemidirectProduct.inr e) = SemidirectProduct.inr e := by
  simp only [originalSemidirectEmbedding, SemidirectProduct.map_inr, MonoidHom.id_apply]

end ModularRep.PaperProofs.TypeBRankThreeMoritaCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
