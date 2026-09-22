import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionData
import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks

/-!
# The identity ambient when a character stabilizer is inner

Literal block support places the full character stabilizer in the actual
block stabilizer. Its inclusion in the canonical inner range makes the
inner embedding surjective, with kernel equal to the centre. The resulting
quotient isomorphism retains the precise opposite-automorphism square.
The original group and identity base embedding require no centreless or
perfect-group hypothesis.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3FaithfulCriterionAmbient

open ModularRep
open TypeBCentralKernelBlockSource
open TypeBQ3PrincipalCriterionData
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms

variable {k K X : Type} [Field k] [Field K] [Group X] [Finite X]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T

variable (root : PrimeRegularRootEmbedding 2 k K X) (phi : IBr root)

/-- The kernel calculation applies even when the original centre is nontrivial. -/
theorem innerEmbedding_ker :
    (innerEmbedding root phi).ker = Subgroup.center X := by
  ext x
  change innerEmbedding root phi x = 1 ↔ x ∈ Subgroup.center X
  rw [Subtype.ext_iff]
  change MulOpposite.op (MulAut.conj x⁻¹) = MulOpposite.op (1 : MulAut X) ↔
    x ∈ Subgroup.center X
  rw [MulOpposite.op_inj]
  change x⁻¹ ∈ (MulAut.conj : X →* MulAut X).ker ↔ x ∈ Subgroup.center X
  rw [conj_ker_eq_center, inv_mem_iff]

/-- Only the full stabilizer of this character needs to be inner. -/
theorem innerEmbedding_surjective_of_inertia_le_inner
    (inertiaInner : MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi ≤
      (RepresentationWeight.innerInverseOpHom (G := X)).range) :
    Function.Surjective (innerEmbedding root phi) := by
  intro a
  refine Exists.elim (inertiaInner a.property) ?_
  intro x hx
  refine ⟨x, Subtype.ext ?_⟩
  change MulOpposite.op (MulAut.conj x⁻¹) = a.val
  exact hx

/-- The quotient map is induced by the literal inner embedding. -/
def quotientEquiv_of_inertia_le_inner
    (inertiaInner : MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi ≤
      (RepresentationWeight.innerInverseOpHom (G := X)).range) :
    X ⧸ Subgroup.center X ≃* ActualAutAmbient root phi :=
  QuotientGroup.liftEquiv (Subgroup.center X)
    (innerEmbedding_surjective_of_inertia_le_inner root phi inertiaInner)
    (innerEmbedding_ker root phi).symm

theorem quotientEquiv_mk
    (inertiaInner : MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi ≤
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (x : X) :
    quotientEquiv_of_inertia_le_inner root phi inertiaInner
      (QuotientGroup.mk' (Subgroup.center X) x) = innerEmbedding root phi x := rfl

/-- This is the opposite action required by the literal criterion target. -/
theorem quotientEquiv_natural
    (inertiaInner : MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi ≤
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (x : X) :
    (quotientEquiv_of_inertia_le_inner root phi inertiaInner
      (QuotientGroup.mk' (Subgroup.center X) x)).val =
        CyclicOuterLemma37Concrete.inverseOpHom (MulAut.conj : X →* MulAut X) x := by
  rw [quotientEquiv_mk]
  rfl

section LiteralBlocks

variable [Fintype (LiteralPrimitiveBlock k X)]
  (D : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k X => b.val))

include D in
/-- The same literal block contains every automorphic image of its character. -/
theorem supported_inertia_le_blockStabilizer
    (b : LiteralPrimitiveBlock k X) (support : Supported root b phi) :
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi ≤
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ b := by
  intro a ha
  have fixed : IrreducibleBrauerCharacter.twist root phi a.unop = phi := ha
  have inBlock : TypeBCentralKernelBrauerBlocks.block root D phi = b :=
    (TypeBCentralKernelBrauerBlocks.supported_iff_block root D b phi).mp support
  have transported := TypeBCentralKernelBrauerBlocks.block_twist root D a.unop phi
  rw [fixed, inBlock] at transported
  change LiteralPrimitiveBlock.rightTwistBlock b a.unop = b
  exact transported.symm

include D in
/-- The specified block stabilizer supplies innerness for this character. -/
theorem supported_inertia_le_inner
    (b : LiteralPrimitiveBlock k X) (support : Supported root b phi)
    (blockInner : MulAction.stabilizer (MulAut X)ᵐᵒᵖ b ≤
      (RepresentationWeight.innerInverseOpHom (G := X)).range) :
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi ≤
      (RepresentationWeight.innerInverseOpHom (G := X)).range :=
  (supported_inertia_le_blockStabilizer root phi D b support).trans blockInner

end LiteralBlocks

/-- The identity ambient uses the entire original group as its base. -/
def identityBaseEquiv (Y : Type) [Group Y] : Y ≃* (⊤ : Subgroup Y) :=
  Subgroup.topEquiv.symm

theorem identityBaseEmbedding (Y : Type) [Group Y] :
    baseEmbedding (⊤ : Subgroup Y) (identityBaseEquiv Y) = MonoidHom.id Y := rfl

theorem identityBaseCentralizer (Y : Type) [Group Y] :
    Subgroup.centralizer ((⊤ : Subgroup Y) : Set Y) = Subgroup.center Y := by
  simpa only [Subgroup.coe_top] using (Subgroup.centralizer_univ (G := Y))

theorem identityBase_conjugation (Y : Type) [Group Y] (x y : Y) :
    baseEmbedding (⊤ : Subgroup Y) (identityBaseEquiv Y) (MulAut.conj x y) =
      x * baseEmbedding (⊤ : Subgroup Y) (identityBaseEquiv Y) y * x⁻¹ := rfl

/-- The local group is computed from the prescribed raw radical itself. -/
theorem identityLocalGroup (R : CharacterWeight 2 K X) :
    localGroup R (⊤ : Subgroup X) (identityBaseEquiv X) =
      Subgroup.normalizer (R.subgroup : Set X) := by
  unfold localGroup
  rw [identityBaseEmbedding, Subgroup.map_id]

theorem identityBase_intermediate_eq_top (J : Subgroup X)
    (hJ : (⊤ : Subgroup X) ≤ J) : J = ⊤ := top_unique hJ

end ModularRep.PaperProofs.TypeBQ3FaithfulCriterionAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
