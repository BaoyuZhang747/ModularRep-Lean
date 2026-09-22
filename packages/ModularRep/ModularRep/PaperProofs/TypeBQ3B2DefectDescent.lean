import ModularRep.PaperProofs.TypeBQ3B2DihedralDefect
import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

/-!
The nominated B2 defect subgroup is carried along the fixed projection from
X to the same matrix G3. Its restriction is injective by the two-group and
prime-to-two kernel conditions, so its group isomorphism type is preserved.

Navarro (9.9)(c), p. 199, identifies the defect groups of an actually dominated
block with the images of the original defect groups. The sole field below
renders that statement together with Navarro (4.11) on the same literal
central Brauer support. The two-group component is derived separately.
The displayed block image and selected ambient idempotent equality are
indices, not conclusions supplied by this source. Their specified source
identification remains E1/U. No weight correspondence is constructed here.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2DefectDescent

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource
open Formalisation.ComputationArithmetic
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

/-- Restriction to the specified two-subgroup is an equivalence onto its image. -/
def pSubgroupImageEquiv
    {A B : Type} [Group A] [Group B]
    (f : A →* B) (primeTo : ¬ 2 ∣ Nat.card f.ker)
    (D : Subgroup A) (isPGroup : IsPGroup 2 D) : D ≃* D.map f :=
  MulEquiv.ofBijective (f.subgroupMap D) ⟨by
    intro x y same
    apply Subtype.ext
    exact injOn_pSubgroup_of_primeTo_ker Nat.prime_two f primeTo D isPGroup
      x.property y.property (congrArg Subtype.val same),
    f.subgroupMap_surjective D⟩

@[simp] theorem pSubgroupImageEquiv_apply
    {A B : Type} [Group A] [Group B]
    (f : A →* B) (primeTo : ¬ 2 ∣ Nat.card f.ker)
    (D : Subgroup A) (isPGroup : IsPGroup 2 D) (x : D) :
    (pSubgroupImageEquiv f primeTo D isPGroup x).val = f x.val := rfl

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

variable [Finite X]
local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]
variable {dX : Q3Block → k[X]}

/-- The fixed specified defect-image statement on the same quotient block. -/
structure Navarro99cDefectImageSource
    (blocksX : BlockIdempotentDecomposition dX)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocksX .B2 D)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (image : algebraMapOf (q matrixSource freeSource) (dX .B2) = b.val) : Prop where
  support_image :
    letI := R.operations.ambientBlockData.fintypeBlock
    Navarro411CentralBrauerSource R.operations.ambientBlockData.blocks b
      (D.map (q matrixSource freeSource))

variable (blocksX : BlockIdempotentDecomposition dX)
  (D : Subgroup X)
  (defect : Navarro411DefectRepresentative (p := 2) blocksX .B2 D)
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (b : LiteralPrimitiveBlock k G3)
  (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
  (image : algebraMapOf (q matrixSource freeSource) (dX .B2) = b.val)
  (source : Navarro99cDefectImageSource matrixSource freeSource
  blocksX D defect R b ambientAt image)

include source in
/-- The image is the nominated actual defect representative downstairs. -/
def mappedDefect :
    letI := R.operations.ambientBlockData.fintypeBlock
    Navarro411DefectRepresentative (p := 2) R.operations.ambientBlockData.blocks b
      (D.map (q matrixSource freeSource)) := by
  letI := R.operations.ambientBlockData.fintypeBlock
  exact ⟨defect.isPGroup.map (q matrixSource freeSource), source.support_image⟩

include defect in
/-- The original D8 isomorphism is transported to this exact image subgroup. -/
theorem mappedDefect_dihedral (dihedral : Nonempty (D ≃* DihedralGroup 4)) :
    Nonempty ((D.map (q matrixSource freeSource)) ≃* DihedralGroup 4) := by
  obtain ⟨equiv⟩ := dihedral
  exact ⟨(pSubgroupImageEquiv (q matrixSource freeSource)
    (q_kernel_primeToTwo matrixSource freeSource) D defect.isPGroup).symm.trans equiv⟩

end ModularRep.PaperProofs.TypeBQ3B2DefectDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
