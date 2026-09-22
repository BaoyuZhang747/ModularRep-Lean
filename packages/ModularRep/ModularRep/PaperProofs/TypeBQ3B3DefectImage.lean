import ModularRep.PaperProofs.TypeBQ3B2DefectDescent
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
The actual order-two B3 defect subgroup is mapped through the retained
projection from X to the same matrix G3. The prime-to-two kernel makes this
restriction injective. Its cardinality, cyclicity and commutativity therefore
follow from the actual order of the nominated subgroup, independently of any
character count.

Navarro (9.9)(c), p. 199, identifies defect groups of the dominated block with
images of the original defect groups. The single source field below records
its Navarro (4.11) central Brauer support at the exact specified block index.
The source is guarded by the literal block image and selected catalogue
identity. Its specified theorem interpretation remains E1/U, while the actual
upstairs order-two identification remains a separate E3/U input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B3DefectImage

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource
open Formalisation.ComputationArithmetic
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

variable [Finite X]
local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]
variable {dX : Q3Block → k[X]}

variable (blocksX : BlockIdempotentDecomposition dX)
  (D : Subgroup X)
  (defect : Navarro411DefectRepresentative (p := 2) blocksX .B3 D)

include defect in
/-- The equivalence is the restriction of the same quotient projection. -/
def defectImageEquiv : D ≃* D.map (q matrixSource freeSource) :=
  TypeBQ3B2DefectDescent.pSubgroupImageEquiv (q matrixSource freeSource)
    (q_kernel_primeToTwo matrixSource freeSource) D defect.isPGroup

@[simp] theorem defectImageEquiv_apply (x : D) :
    (defectImageEquiv matrixSource freeSource blocksX D defect x).val =
      q matrixSource freeSource x.val := rfl

include defect in
/-- The specified order-two input is preserved on the literal image subgroup. -/
theorem mappedDefect_card_two (cardD : Nat.card D = 2) :
    Nat.card (D.map (q matrixSource freeSource)) = 2 :=
  (Nat.card_congr
    (defectImageEquiv matrixSource freeSource blocksX D defect).toEquiv).symm.trans cardD

include defect in
/-- Prime cardinality gives cyclicity without a separate cyclic-defect source. -/
theorem mappedDefect_isCyclic (cardD : Nat.card D = 2) :
    IsCyclic (D.map (q matrixSource freeSource)) :=
  isCyclic_of_prime_card
    (mappedDefect_card_two matrixSource freeSource blocksX D defect cardD)

include defect in
/-- The same actual image defect group is commutative. -/
theorem mappedDefect_isMulCommutative (cardD : Nat.card D = 2) :
    IsMulCommutative (D.map (q matrixSource freeSource)) :=
  @IsCyclic.isMulCommutative (D.map (q matrixSource freeSource)) _
    (mappedDefect_isCyclic matrixSource freeSource blocksX D defect cardD)

/-- Navarro defect-image support on the same specified dominated block. -/
structure Navarro99cDefectImageSource
    (blocksX : BlockIdempotentDecomposition dX)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocksX .B3 D)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (image : algebraMapOf (q matrixSource freeSource) (dX .B3) = b.val) : Prop where
  support_image :
    letI := R.operations.ambientBlockData.fintypeBlock
    Navarro411CentralBrauerSource R.operations.ambientBlockData.blocks b
      (D.map (q matrixSource freeSource))

variable (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (b : LiteralPrimitiveBlock k G3)
  (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
  (image : algebraMapOf (q matrixSource freeSource) (dX .B3) = b.val)
  (source : Navarro99cDefectImageSource matrixSource freeSource
    blocksX D defect R b ambientAt image)

include source in
/-- The image is the nominated Navarro defect representative downstairs. -/
def mappedDefect :
    letI := R.operations.ambientBlockData.fintypeBlock
    Navarro411DefectRepresentative (p := 2) R.operations.ambientBlockData.blocks b
      (D.map (q matrixSource freeSource)) := by
  letI := R.operations.ambientBlockData.fintypeBlock
  exact ⟨defect.isPGroup.map (q matrixSource freeSource), source.support_image⟩

end ModularRep.PaperProofs.TypeBQ3B3DefectImage


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
