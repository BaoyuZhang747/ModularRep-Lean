import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
import ModularRep.PaperProofs.TypeBCentralKernelInertia
import ModularRep.IBrBlockAutomorphism

/-! Named block fibres and literal support carry the same Brauer character.
The conversion uses the named specified idempotent and no weight catalogue. -/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3FaithfulFibreBinding

open ModularRep ModularRep.FDRepSimpleClassKZero
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

universe u

variable {p : Nat} {k K X NamedBlock : Type u}
variable [Field k] [Field K] [Group X] [Finite X]
variable [CharP k p] [IsAlgClosed k] [CharZero K] [Fintype NamedBlock]
variable (root : PrimeRegularRootEmbedding p k K X)
  (hinj : IrreducibleBrauerCharacterInjectivity root)
  {d : NamedBlock → k[X]} (blocks : BlockIdempotentDecomposition d)
  (i : NamedBlock)

/-- Literal support is equivalent to membership in the named specified block. -/
theorem supported_iff_namedBlock (phi : IBr root) :
    Supported root (⟨d i, blocks.primitive i⟩ : LiteralPrimitiveBlock k X) phi ↔
      irreducibleBrauerCharacterBlock root hinj blocks phi = i := by
  constructor
  · rintro ⟨V, hV, hchar, hsupp⟩
    letI : IsSimpleModule k[X] (Representation.asModule V.ρ) :=
      (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
    have hi : i = blocks.moduleBlock (V := Representation.asModule V.ρ) := by
      apply blocks.moduleBlock_eq_of_smul_eq_self
      intro v
      apply (Representation.asModuleEquiv V.ρ).injective
      rw [Representation.asModuleEquiv_map_smul, hsupp]
      rfl
    have hblock : irreducibleBrauerCharacterBlock root hinj blocks phi =
        blocks.moduleBlock (V := Representation.asModule V.ρ) :=
      blocks.moduleBlock_eq_of_smul_eq_self
        (block_smul_of_affording root hinj blocks phi V hV hchar)
    exact hblock.trans hi.symm
  · intro selected
    obtain ⟨V, hV, hchar⟩ := phi.property
    refine ⟨V, hV, hchar, ?_⟩
    apply LinearMap.ext
    intro v
    have acts := block_smul_of_affording root hinj blocks phi V hV hchar
      ((Representation.asModuleEquiv V.ρ).symm v)
    rw [selected] at acts
    have values := congrArg (Representation.asModuleEquiv V.ρ) acts
    change Representation.asAlgebraHom V.ρ (d i) v = v
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] using values

/-- The fibre equivalence preserves the literal underlying Brauer character. -/
def brauerFibreEquiv :
    IBrBlock root hinj blocks i ≃
      BrauerFibre root (⟨d i, blocks.primitive i⟩ : LiteralPrimitiveBlock k X) where
  toFun phi := ⟨phi.val, (supported_iff_namedBlock root hinj blocks i phi.val).mpr phi.property⟩
  invFun phi := ⟨phi.val, (supported_iff_namedBlock root hinj blocks i phi.val).mp phi.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem brauerFibreEquiv_apply_val (phi : IBrBlock root hinj blocks i) :
    (brauerFibreEquiv root hinj blocks i phi).val = phi.val := rfl

@[simp] theorem brauerFibreEquiv_symm_apply_val
    (phi : BrauerFibre root (⟨d i, blocks.primitive i⟩ : LiteralPrimitiveBlock k X)) :
    ((brauerFibreEquiv root hinj blocks i).symm phi).val = phi.val := rfl

/-- A character stabilizer lies in the stabilizer of its named literal block. -/
theorem inertia_le_namedBlockStabilizer (phi : IBrBlock root hinj blocks i) :
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi.val ≤
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ
        (⟨d i, blocks.primitive i⟩ : LiteralPrimitiveBlock k X) := by
  intro alpha fixed
  have h := primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
    root hinj blocks alpha phi.val
  have same : alpha • phi.val = phi.val := fixed
  rw [same, phi.property] at h
  exact h.symm

end ModularRep.PaperProofs.TypeBQ3FaithfulFibreBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
