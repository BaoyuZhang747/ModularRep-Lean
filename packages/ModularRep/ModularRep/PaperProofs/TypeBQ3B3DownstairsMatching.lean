import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBLiteralBlockReindex
import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks
import ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
import ModularRep.PaperProofs.TypeBQ3FaithfulFibreBinding

/-!
# The specified B3 singleton and its intrinsic matching graph

The complete character dictionary and its literal block membership identify
B3's sole printed label L15 with the complete actual supported Brauer fibre.
The same reference can be used in the retained central quotient construction.
Trivial-sector, quotient-root and specified block-image obligations remain at
that construction's existing interfaces.

On an actual G3 block, two proved singleton cardinalities construct a matching.
For its intrinsic graph, an equality between two supported characters implies
that the displayed actor stabilizes their specified block. The singleton
weight fibre then gives the required equality on actual weight classes.
No global block stability or outer-character action is assumed or asserted.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B3DownstairsMatching

open ModularRep FDRepSimpleClassKZero CharacterWeight
open Formalisation.ComputationArithmetic
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open TypeBQ3TripleCoverCarrier TypeBCentralKernelInertia
open TypeBExceptionalQ3Proposition416Actual

variable {k K : Type} [Field k] [Field K] [CharZero K]
  [CharP k 2] [IsAlgClosed k]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

section Table

variable [Finite X]
  (root : PrimeRegularRootEmbedding 2 k K X)
  {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)
  (brauerMap : LiteralBrauerOutputMap root)
  (map_injective : Function.Injective brauerMap.character)
  (map_surjective : Function.Surjective brauerMap.character)
  (compatible : BrauerBlockFibreCompatible root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)

/-- The actual reference is exactly the character at printed position L15. -/
def reference : BrauerFibre root (primitiveBlockOfLabel blocks .B3) :=
  TypeBQ3FaithfulFibreBinding.brauerFibreEquiv root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks .B3
    ⟨brauerMap.character .L15, compatible .L15⟩

@[simp] theorem reference_val :
    (reference root blocks brauerMap compatible).val = brauerMap.character .L15 := rfl

/-- The complete table dictionary restricts to the same specified B3 fibre. -/
def tableEquiv :
    BrauerOutputFibre .B3 ≃ BrauerFibre root (primitiveBlockOfLabel blocks .B3) :=
  (brauerBlockFibreEquiv root (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    blocks brauerMap map_injective map_surjective compatible .B3).trans
    (TypeBQ3FaithfulFibreBinding.brauerFibreEquiv root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks .B3)

include map_injective map_surjective compatible in
/-- The finite L15 calculation counts the complete actual supported fibre. -/
theorem brauer_card : Nat.card (BrauerFibre root (primitiveBlockOfLabel blocks .B3)) = 1 := by
  calc
    Nat.card (BrauerFibre root (primitiveBlockOfLabel blocks .B3)) =
        Nat.card (BrauerOutputFibre .B3) :=
      Nat.card_congr (tableEquiv root blocks brauerMap
        map_injective map_surjective compatible).symm
    _ = Fintype.card (BrauerOutputFibre .B3) := Nat.card_eq_fintype_card
    _ = 1 := brauerOutputFibre_card .B3

include map_injective map_surjective in
/-- Uniqueness is within this specified block; it is not global actor fixation. -/
theorem brauer_eq_reference
    (phi : BrauerFibre root (primitiveBlockOfLabel blocks .B3)) :
    phi = reference root blocks brauerMap compatible := by
  letI : Subsingleton (BrauerFibre root (primitiveBlockOfLabel blocks .B3)) :=
    (Nat.card_eq_one_iff_unique.mp
      (brauer_card root blocks brauerMap map_injective map_surjective compatible)).1
  exact Subsingleton.elim _ _

end Table

section Matching

variable (root : PrimeRegularRootEmbedding 2 k K G3)
  (R : LocalBlockInductionSource (p := 2) (k := k) (K := K) (G := G3)
    (Block := LiteralPrimitiveBlock k G3))
  (b : LiteralPrimitiveBlock k G3)

include R in
/-- An actor relating two characters in the same supported fibre stabilizes
that literal block. The complete decomposition is constructed from R. -/
theorem block_fixed_of_supported_values
    (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b)
    (values : psi.val = alpha • phi.val) :
    LiteralPrimitiveBlock.rightTwistBlock b alpha.unop = b := by
  letI : Fintype (LiteralPrimitiveBlock k G3) := R.operations.ambientBlockData.fintypeBlock
  let physicalBlocks := TypeBLiteralBlockReindex.literalBlocks R.operations.ambientBlockData.blocks
  have hphi : TypeBCentralKernelBrauerBlocks.block root physicalBlocks phi.val = b :=
    (TypeBCentralKernelBrauerBlocks.supported_iff_block root physicalBlocks b phi.val).mp
      phi.property
  have hpsi : TypeBCentralKernelBrauerBlocks.block root physicalBlocks psi.val = b :=
    (TypeBCentralKernelBrauerBlocks.supported_iff_block root physicalBlocks b psi.val).mp
      psi.property
  have transported :=
    TypeBCentralKernelBrauerBlocks.block_twist root physicalBlocks alpha.unop phi.val
  have twist : IrreducibleBrauerCharacter.twist root phi.val alpha.unop = psi.val := values.symm
  rw [twist, hphi, hpsi] at transported
  exact transported.symm

/-- Proved singleton fibres construct the exact intrinsic graph required by
local criterion construction, with no separate action or matching source. -/
theorem exists_equivariant_matching
    (brauer_card : Nat.card (BrauerFibre root b) = 1)
    (weight_card : Nat.card (R.Fibre b) = 1) :
    ∃ omega : BrauerFibre root b ≃ R.Fibre b,
      ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
        psi.val = alpha • phi.val →
          (omega psi).val = alpha • (omega phi).val := by
  have brauerSingleton := Nat.card_eq_one_iff_unique.mp brauer_card
  have weightSingleton := Nat.card_eq_one_iff_unique.mp weight_card
  letI : Subsingleton (BrauerFibre root b) := brauerSingleton.1
  letI : Subsingleton (R.Fibre b) := weightSingleton.1
  let omega : BrauerFibre root b ≃ R.Fibre b := {
    toFun := fun _ => Classical.choice weightSingleton.2
    invFun := fun _ => Classical.choice brauerSingleton.2
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }
  refine ⟨omega, ?_⟩
  intro alpha phi psi values
  let actor : MulAction.stabilizer (MulAut G3)ᵐᵒᵖ b := ⟨alpha, by
    change LiteralPrimitiveBlock.rightTwistBlock b alpha.unop = b
    exact block_fixed_of_supported_values root R b alpha phi psi values⟩
  have same : omega psi = actor • omega phi := Subsingleton.elim _ _
  exact congrArg Subtype.val same

end Matching

end ModularRep.PaperProofs.TypeBQ3B3DownstairsMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
