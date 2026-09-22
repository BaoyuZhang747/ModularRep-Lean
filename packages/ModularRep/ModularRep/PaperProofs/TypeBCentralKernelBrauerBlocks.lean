import ModularRep.PaperProofs.TypeBCentralKernelBlockSource
import ModularRep.IBrBlockEquivTransport
import ModularRep.IBrBlockAutomorphism

/-!
# Identification with the checked specified Brauer block catalogue

The existential module support used by the central-kernel proof is exactly
membership in the existing `IBrBlock` carrier. This join is proved using
checked Brauer-character separation and simple-module support. There is no
new literature input or freely labelled block map.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks

open FDRepSimpleClassKZero TypeBCentralKernelBlockSource

universe u

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G] [Fintype (LiteralPrimitiveBlock k G)]

variable (iota : PrimeRegularRootEmbedding p k K G)
  (D : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))

/-- Character separation is already checked for the prescribed root. -/
abbrev injective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota

def block (phi : IBr iota) : LiteralPrimitiveBlock k G :=
  irreducibleBrauerCharacterBlock iota (injective iota) D phi

theorem block_of_affording (phi : IBr iota) (V : FDRep k G)
    (hV : Representation.IsIrreducible V.ρ)
    (hchar : phi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota) :
    letI : IsSimpleModule k[G] (Representation.asModule V.ρ) :=
      (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
    block iota D phi = D.moduleBlock (V := Representation.asModule V.ρ) := by
  letI : IsSimpleModule k[G] (Representation.asModule V.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
  have hphi : simpleClassToIBr iota (simpleClassOfIrreducibleFDRep V hV) = phi := by
    apply Subtype.ext
    change Representation.brauerCharacterOfRootEmbedding
      (simpleClassFDRep (simpleClassOfIrreducibleFDRep V hV)).ρ iota = phi.val
    rw [hchar]
    exact Representation.brauerCharacterOfRootEmbedding_iso iota
      (simpleClassOfIrreducibleFDRepIso V hV)
  change irreducibleBrauerCharacterBlock iota (injective iota) D phi = _
  rw [← hphi, irreducibleBrauerCharacterBlock_simpleClassToIBr]
  exact simpleModuleClassBlock_simpleClassOfIrreducibleFDRep D V hV

theorem supported_iff_block (b : LiteralPrimitiveBlock k G) (phi : IBr iota) :
    Supported iota b phi ↔ block iota D phi = b := by
  constructor
  · rintro ⟨V, hV, hchar, hsupp⟩
    letI : IsSimpleModule k[G] (Representation.asModule V.ρ) :=
      (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
    rw [block_of_affording iota D phi V hV hchar]
    symm
    apply D.moduleBlock_eq_of_smul_eq_self
    intro v
    apply (Representation.asModuleEquiv V.ρ).injective
    rw [Representation.asModuleEquiv_map_smul, hsupp]
    rfl
  · intro hb
    obtain ⟨V, hV, hchar⟩ := phi.2
    letI : IsSimpleModule k[G] (Representation.asModule V.ρ) :=
      (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
    refine ⟨V, hV, hchar, ?_⟩
    have hblock := (block_of_affording iota D phi V hV hchar).symm.trans hb
    apply LinearMap.ext
    intro v
    have hsupp := D.moduleBlock_smul (V := Representation.asModule V.ρ)
      ((Representation.asModuleEquiv V.ρ).symm v)
    rw [hblock] at hsupp
    have heq := congrArg (Representation.asModuleEquiv V.ρ) hsupp
    change Representation.asAlgebraHom V.ρ b.val v = v
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] using heq

/-- The support subtype and the library block fibre have the same underlying
actual Brauer character. -/
def supportedEquivIBrBlock (b : LiteralPrimitiveBlock k G) :
    {phi : IBr iota // Supported iota b phi} ≃ IBrBlock iota (injective iota) D b where
  toFun phi := ⟨phi.val, (supported_iff_block iota D b phi.val).mp phi.property⟩
  invFun phi := ⟨phi.val, (supported_iff_block iota D b phi.val).mpr phi.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem block_twist (alpha : MulAut G) (phi : IBr iota) :
    block iota D (IrreducibleBrauerCharacter.twist iota phi alpha) =
      LiteralPrimitiveBlock.rightTwistBlock (block iota D phi) alpha := by
  exact primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
    iota (injective iota) D (MulOpposite.op alpha) phi

include D in
theorem supported_twist (b : LiteralPrimitiveBlock k G) (alpha : MulAut G)
    (phi : IBr iota) (h : Supported iota b phi) :
    Supported iota (LiteralPrimitiveBlock.rightTwistBlock b alpha)
      (IrreducibleBrauerCharacter.twist iota phi alpha) := by
  rw [supported_iff_block iota D, block_twist iota D,
    (supported_iff_block iota D b phi).mp h]

end ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
