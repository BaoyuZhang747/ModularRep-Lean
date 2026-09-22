import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBLiteralBlockReindex
import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks

/-!
Matching on an arbitrary literal block of the actual matrix Omega over ZMod 3.
The Brauer and weight counts and their proved fixedness are consumed on those
complete fibres. A supported Brauer character exists by the count, so its
fixedness forces stability of its specified block under every automorphism.

The specified decomposition used for this support argument is constructed
from the complete catalogue stored by R. No correspondence, block-stability
assumption, or named nine-block dictionary is supplied. The result states
equivariance directly on the underlying characters and weight classes.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3B2DownstairsMatching

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBCentralKernelInertia

variable {k K : Type} [Field k] [Field K] [CharZero K]
  [CharP k 2] [IsAlgClosed k]

local instance groupFintype : Fintype G3 :=
  TypeBRankThreePrincipalCountBinding.groupFintype G3

variable (root : PrimeRegularRootEmbedding 2 k K G3)
  (R : LocalBlockInductionSource (p := 2) (k := k) (K := K) (G := G3)
    (Block := LiteralPrimitiveBlock k G3))
  (b : LiteralPrimitiveBlock k G3)

include R in
/-- Nonempty specified support and character fixedness force literal block
stability. The reindexing uses the existing complete catalogue of R. -/
theorem block_fixed_of_brauer_fixed
    (brauer_card : Nat.card (BrauerFibre root b) = 2)
    (brauer_fixed : ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi : BrauerFibre root b),
      alpha • phi.val = phi.val) :
    ∀ alpha : (MulAut G3)ᵐᵒᵖ,
      LiteralPrimitiveBlock.rightTwistBlock b alpha.unop = b := by
  letI : Fintype (LiteralPrimitiveBlock k G3) :=
    R.operations.ambientBlockData.fintypeBlock
  let physicalBlocks :=
    TypeBLiteralBlockReindex.literalBlocks R.operations.ambientBlockData.blocks
  have inhabited : Nonempty (BrauerFibre root b) :=
    (Nat.card_ne_zero.mp (by rw [brauer_card]; decide)).1
  obtain ⟨phi⟩ := inhabited
  have support : TypeBCentralKernelBrauerBlocks.block root physicalBlocks phi.val = b :=
    (TypeBCentralKernelBrauerBlocks.supported_iff_block root physicalBlocks b phi.val).mp
      phi.property
  intro alpha
  have fixed : IrreducibleBrauerCharacter.twist root phi.val alpha.unop = phi.val :=
    brauer_fixed alpha phi
  have transported :=
    TypeBCentralKernelBrauerBlocks.block_twist root physicalBlocks alpha.unop phi.val
  rw [fixed, support] at transported
  exact transported.symm

/-- The finite equivalence has the intrinsic all-automorphism graph on the
same literal character and weight fibres. -/
theorem exists_equivariant_matching
    (brauer_card : Nat.card (BrauerFibre root b) = 2)
    (weight_card : Nat.card (R.Fibre b) = 2)
    (brauer_fixed : ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi : BrauerFibre root b),
      alpha • phi.val = phi.val)
    (weight_fixed : ∀ (alpha : MulAction.stabilizer (MulAut G3)ᵐᵒᵖ b)
      (weight : R.Fibre b), alpha • weight = weight) :
    ∃ omega : BrauerFibre root b ≃ R.Fibre b,
      ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
        psi.val = alpha • phi.val →
          (omega psi).val = alpha • (omega phi).val := by
  classical
  letI : Finite (BrauerFibre root b) :=
    Nat.finite_of_card_ne_zero (by rw [brauer_card]; decide)
  letI : Finite (R.Fibre b) :=
    Nat.finite_of_card_ne_zero (by rw [weight_card]; decide)
  letI : Fintype (BrauerFibre root b) := Fintype.ofFinite _
  letI : Fintype (R.Fibre b) := Fintype.ofFinite _
  have card_eq : Fintype.card (BrauerFibre root b) = Fintype.card (R.Fibre b) := by
    simpa only [← Nat.card_eq_fintype_card] using brauer_card.trans weight_card.symm
  let omega : BrauerFibre root b ≃ R.Fibre b := Fintype.equivOfCardEq card_eq
  have block_fixed := block_fixed_of_brauer_fixed root R b brauer_card brauer_fixed
  refine ⟨omega, ?_⟩
  intro alpha phi psi values
  have same : psi = phi := Subtype.ext (values.trans (brauer_fixed alpha phi))
  subst psi
  let actor : MulAction.stabilizer (MulAut G3)ᵐᵒᵖ b := ⟨alpha, by
    change LiteralPrimitiveBlock.rightTwistBlock b alpha.unop = b
    exact block_fixed alpha⟩
  have fixed := weight_fixed actor (omega phi)
  have fixedValues := congrArg Subtype.val fixed
  change alpha • (omega phi).val = (omega phi).val at fixedValues
  exact fixedValues.symm

end ModularRep.PaperProofs.TypeBQ3B2DownstairsMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
