import ModularRep.LinearBlockStabilizer
import ModularRep.PaperProofs.TypeCExactStabilizerLemma310Relative

/-!
# A block stabiliser in a tensor and field action

The kernel of the field projection on a block stabiliser embeds in the
stabiliser of that block under linear characters. The general central
character argument therefore bounds its order by the index of `NZ(G)`.

The tensor action is interpreted by the simple modules in the block. If a
convention uses inverse tensoring, the map `linear` is the reciprocal
character map. It is injective and has the same kernel on `N`.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ManuscriptIBAW

open ModularRep ModularRep.LinearBlockStabilizer
open ModularRep.PaperProofs.TypeCExactStabilizerLemma310Relative
open ModularRep.IntegralBasicSetBridge

universe u v

variable {C E B : Type v} [Group C] [Group E]
    (field : E →* MulAut C) [MulAction (C ⋊[field] E) B]

@[instance_reducible] def tensorBlockAction : MulAction C B :=
  MulAction.compHom B (SemidirectProduct.inl : C →* C ⋊[field] E)

/-- Send a kernel element to its linear character coordinate. -/
def tensorKernelToStabilizer (b : B) :
    let _ := tensorBlockAction (B := B) field
    (fieldProjection field (MulAction.stabilizer (C ⋊[field] E) b)).ker →
      MulAction.stabilizer C b := by
  dsimp only
  let _ := tensorBlockAction (B := B) field
  intro x
  refine ⟨x.1.1.left, ?_⟩
  have hr : x.1.1.right = 1 := x.2
  have hx : (SemidirectProduct.inl x.1.1.left : C ⋊[field] E) = x.1.1 := by
    apply SemidirectProduct.ext
    · rfl
    · exact hr.symm
  change (SemidirectProduct.inl x.1.1.left : C ⋊[field] E) • b = b
  rw [hx]
  exact x.1.2

theorem tensorKernelToStabilizer_injective (b : B) :
    let _ := tensorBlockAction (B := B) field
    Function.Injective (tensorKernelToStabilizer field b) := by
  dsimp only
  let _ := tensorBlockAction (B := B) field
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact congrArg Subtype.val h
  · exact x.2.trans y.2.symm

section PrimitiveBlocks

variable {ell : ℕ} {G k : Type v} [Group G] [Finite G]
    [Field k] [CharP k ell] [IsAlgClosed k]
    [Finite C] [Finite E] [IsCyclic E]
    [MulAction (C ⋊[field] E) (LiteralPrimitiveBlock k G)]

omit [Finite E] [IsCyclic E] in
/-- The order bound in Lemma 3.10 follows from the general linear character
lemma, with the same primitive block and tensor action. -/
theorem tensor_field_kernel_bound
    (prime : ell.Prime) (N : Subgroup G) [N.Normal]
    (linear : C →* (G →* kˣ)) (injective : Function.Injective linear)
    (trivialOnN : ∀ c, N ≤ (linear c).ker)
    (source : let _ := tensorBlockAction (B := LiteralPrimitiveBlock k G) field
      SimpleBlockTensorSource linear)
    (b : LiteralPrimitiveBlock k G) :
    Nat.card (fieldProjection field (MulAction.stabilizer (C ⋊[field] E) b)).ker ≤
      Nat.card (G ⧸ (N ⊔ Subgroup.center G)) := by
  let _ := tensorBlockAction (B := LiteralPrimitiveBlock k G) field
  have hbound := (modular_block_stabilizer_bound prime N linear injective trivialOnN source b).2
  exact (Nat.card_le_card_of_injective (tensorKernelToStabilizer field b)
    (tensorKernelToStabilizer_injective field b)).trans hbound

/-- An index at most two gives the precise normal kernel, cyclic quotient
and hypoelementary conclusion needed for Conlon's theorem. -/
theorem tensor_field_stabilizer_hypoelementary
    (prime : ell.Prime) (N : Subgroup G) [N.Normal]
    (linear : C →* (G →* kˣ)) (injective : Function.Injective linear)
    (trivialOnN : ∀ c, N ≤ (linear c).ker)
    (source : let _ := tensorBlockAction (B := LiteralPrimitiveBlock k G) field
      SimpleBlockTensorSource linear)
    (index : Nat.card (G ⧸ (N ⊔ Subgroup.center G)) ≤ 2)
    (b : LiteralPrimitiveBlock k G) :
    IsPHypoelementary 2 (MulAction.stabilizer (C ⋊[field] E) b) := by
  exact exactStabilizer_isTwoHypoelementary field _
    ((tensor_field_kernel_bound field prime N linear injective trivialOnN source b).trans index)

/-- The full conclusion for the same block stabiliser and its tensor
kernel, including every subgroup needed by the mark argument. -/
theorem tensor_field_stabilizer_structure
    (prime : ell.Prime) (N : Subgroup G) [N.Normal]
    (linear : C →* (G →* kˣ)) (injective : Function.Injective linear)
    (trivialOnN : ∀ c, N ≤ (linear c).ker)
    (source : let _ := tensorBlockAction (B := LiteralPrimitiveBlock k G) field
      SimpleBlockTensorSource linear)
    (index : Nat.card (G ⧸ (N ⊔ Subgroup.center G)) ≤ 2)
    (b : LiteralPrimitiveBlock k G) :
    let J := MulAction.stabilizer (C ⋊[field] E) b
    let D := (fieldProjection field J).ker
    Nat.card D ≤ 2 ∧ D.Normal ∧ IsCyclic (J ⧸ D) ∧
      ∀ U : Subgroup J, IsPHypoelementary 2 U := by
  dsimp only
  have bound := (tensor_field_kernel_bound field prime N linear injective trivialOnN source b).trans index
  exact ⟨bound, inferInstance, exactStabilizer_quotient_isCyclic field _,
    exactStabilizer_subgroup_isTwoHypoelementary field _ bound⟩

end PrimitiveBlocks

end ManuscriptIBAW

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
