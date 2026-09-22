import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
import ModularRep.PaperProofs.TypeBLocalOrdinaryGeometry

/-!
# Actual symplectic carriers for the odd-prime criterion

The normal subgroup is the range of the previously constructed matrix Sp
inclusion in the literal conformal symplectic matrix group. Its equivalence
with the original Sp, field preservation and natural ambient action are
constructed here. The coefficient prime does not enter these constructions.

The separate structural source is restricted to odd fields and rank at
least three. It supplies standard finite group structural facts on exactly
these maps (Li Section 2.B/Section 5 and the canonical source registry).
It contains no character map, stabilizer factorization, extension or final
block condition. Normality remains an explicit standard structural input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers

open ModularRep
open OddTwoConformalProjectiveRealisation (Sp CSp spEmbedding spEmbedding_injective)
open TypeBCriterionHypotheses

variable (n : ℕ) (F : Type) [Field F]

/-- The same matrix subgroup, now in the criterion's subgroup presentation. -/
def SpSubgroup : Subgroup (CSp n F) := (spEmbedding n F).range

/-- This equivalence is induced by the actual inclusion, with no free map. -/
def spEquiv : Sp n F ≃* SpSubgroup n F :=
  MonoidHom.ofInjective (spEmbedding_injective n F)

@[simp] theorem spEquiv_coe (g : Sp n F) :
    (spEquiv n F g : CSp n F) = spEmbedding n F g := rfl

@[simp] theorem spEquiv_symm_embedding (g : SpSubgroup n F) :
    spEmbedding n F ((spEquiv n F).symm g) = g :=
  MonoidHom.apply_ofInjective_symm (spEmbedding_injective n F) g

/-- The actual ring-automorphism group acts entrywise on the same matrices. -/
abbrev fieldAction : (F ≃+* F) →* MulAut (CSp n F) :=
  OddTwoConformalProjectiveRealisation.cspFieldAction

theorem field_preserves_sp (e : F ≃+* F) (g : CSp n F)
    (hg : g ∈ SpSubgroup n F) :
    fieldAction n F e g ∈ SpSubgroup n F := by
  obtain ⟨x, rfl⟩ := hg
  refine ⟨OddTwoConformalProjectiveRealisation.spFieldAut e x, ?_⟩
  exact (OddTwoConformalProjectiveRealisation.field_spEmbedding e x).symm

/-- Exact setwise invariance consumed by the existing tensor/field adapter. -/
theorem field_spSubgroup_map :
    TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant
      (SpSubgroup n F) (fieldAction n F) := by
  intro e
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact field_preserves_sp n F e g hg
  · intro g hg
    refine ⟨fieldAction n F e⁻¹ g, field_preserves_sp n F e⁻¹ g hg, ?_⟩
    change fieldAction n F e (fieldAction n F e⁻¹ g) = g
    rw [map_inv]
    exact (fieldAction n F e).apply_symm_apply g

def spFieldAut (e : F ≃+* F) : MulAut (SpSubgroup n F) where
  toFun g := ⟨fieldAction n F e g.1, field_preserves_sp n F e g.1 g.2⟩
  invFun g := ⟨fieldAction n F e⁻¹ g.1, field_preserves_sp n F e⁻¹ g.1 g.2⟩
  left_inv g := by
    apply Subtype.ext
    change fieldAction n F e⁻¹ (fieldAction n F e g.1) = g.1
    rw [map_inv]
    exact (fieldAction n F e).symm_apply_apply g.1
  right_inv g := by
    apply Subtype.ext
    change fieldAction n F e (fieldAction n F e⁻¹ g.1) = g.1
    rw [map_inv]
    exact (fieldAction n F e).apply_symm_apply g.1
  map_mul' g h := Subtype.ext ((fieldAction n F e).map_mul g.1 h.1)

def spFieldAction : (F ≃+* F) →* MulAut (SpSubgroup n F) where
  toFun := spFieldAut n F
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change fieldAction n F 1 g.1 = g.1
    rw [map_one]
    rfl
  map_mul' e d := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change fieldAction n F (e * d) g.1 =
      fieldAction n F e (fieldAction n F d g.1)
    rw [map_mul]
    rfl

@[simp] theorem spFieldAction_coe (e : F ≃+* F) (g : SpSubgroup n F) :
    (spFieldAction n F e g : CSp n F) = fieldAction n F e g.1 := rfl

/-- Field transport through the actual matrix inclusion preserves the
original Sp element, not merely its abstract subgroup label. -/
theorem spEquiv_field (e : F ≃+* F) (g : Sp n F) :
    spFieldAction n F e (spEquiv n F g) =
      spEquiv n F (OddTwoConformalProjectiveRealisation.spFieldAut e g) := by
  apply Subtype.ext
  exact OddTwoConformalProjectiveRealisation.field_spEmbedding e g

variable [(SpSubgroup n F).Normal]

/-- Actual conjugation after entrywise field automorphism. -/
def ambientAutomorphism : Ambient (fieldAction n F) →* MulAut (SpSubgroup n F) where
  toFun a := MulAut.conjNormal (H := SpSubgroup n F) a.left * spFieldAction n F a.right
  map_one' := by simp
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (a.left * fieldAction n F a.right b.left) *
        fieldAction n F (a.right * b.right) x.1 *
          (a.left * fieldAction n F a.right b.left)⁻¹ =
      a.left * fieldAction n F a.right
        (b.left * fieldAction n F b.right x.1 * b.left⁻¹) * a.left⁻¹
    simp only [map_mul, MulAut.mul_apply, map_inv, mul_inv_rev]
    group

@[simp] theorem ambientAutomorphism_coe
    (a : Ambient (fieldAction n F)) (g : SpSubgroup n F) :
    (ambientAutomorphism n F a g : CSp n F) =
      a.left * fieldAction n F a.right g.1 * a.left⁻¹ := rfl

@[simp] theorem ambientAutomorphism_inl (m : CSp n F) :
    ambientAutomorphism n F (SemidirectProduct.inl m) =
      MulAut.conjNormal (H := SpSubgroup n F) m := by
  simp [ambientAutomorphism]

@[simp] theorem ambientAutomorphism_inr (e : F ≃+* F) :
    ambientAutomorphism n F (SemidirectProduct.inr e) = spFieldAction n F e := by
  simp [ambientAutomorphism]

/-- The criterion's natural action is computed, not an extra source field. -/
def naturalAction : NaturalAction (SpSubgroup n F) (fieldAction n F) where
  hom := ambientAutomorphism n F
  value := ambientAutomorphism_coe n F

variable [Finite F]

/-- Ring automorphisms inject into the finite set of functions on F. -/
instance fieldAutFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

/-- Kernel equals the centralizer of the same embedded subgroup, before
the structural source identifies that centralizer with embedded Z(CSp). -/
theorem kernel_eq_centralizer :
    (ambientAutomorphism n F).ker =
      Subgroup.centralizer
        (embeddedG (SpSubgroup n F) (fieldAction n F) :
          Set (Ambient (fieldAction n F))) := by
  ext a
  rw [Subgroup.mem_centralizer_iff]
  change ambientAutomorphism n F a = 1 ↔ _
  constructor
  · intro ha x hx
    obtain ⟨g, rfl⟩ := hx
    have h := TypeBLocalOrdinaryGeometry.baseEmbedding_natural
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) a g
    have hg : (naturalAction n F).hom a g = g := by
      change ambientAutomorphism n F a g = g
      rw [ha]
      rfl
    rw [hg] at h
    have heq := congrArg (fun y : Ambient (fieldAction n F) => y * a) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq
  · intro h
    apply MulEquiv.ext
    intro g
    apply TypeBLocalOrdinaryGeometry.baseEmbedding_injective
      (SpSubgroup n F) (fieldAction n F)
    change baseEmbedding (SpSubgroup n F) (fieldAction n F)
        ((naturalAction n F).hom a g) = _
    rw [TypeBLocalOrdinaryGeometry.baseEmbedding_natural]
    rw [← h _ ⟨g, rfl⟩]
    simp [mul_assoc]

/-- Exact standard finite group facts for Li's rank-at-least-three odd-field
setup. The source neither contains nor refers to a character/block target. -/
structure StructuralSource : Prop where
  rank : 3 ≤ n
  field_odd : Odd (Nat.card F)
  field_cyclic : IsCyclic (F ≃+* F)
  derived : commutator (CSp n F) = SpSubgroup n F
  quotient_cyclic : IsCyclic (CSp n F ⧸ SpSubgroup n F)
  centralizer : Subgroup.centralizer
      (embeddedG (SpSubgroup n F) (fieldAction n F) :
        Set (Ambient (fieldAction n F))) = embeddedCenter (fieldAction n F)
  surjective : Function.Surjective (ambientAutomorphism n F)
  outer_abelian : IsMulCommutative (OuterAutomorphism (SpSubgroup n F))

/-- Supply the literal criterion structural clause on these same matrices. -/
theorem structural (source : StructuralSource n F) :
    Structural (SpSubgroup n F) (fieldAction n F) (naturalAction n F) := by
  letI := source.field_cyclic
  exact {
    derived := source.derived
    acting_abelian := inferInstance
    quotient_cyclic := source.quotient_cyclic
    centralizer := source.centralizer
    natural_kernel := (kernel_eq_centralizer n F).trans source.centralizer
    natural_surjective := source.surjective
    outer_abelian := source.outer_abelian }

end ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
