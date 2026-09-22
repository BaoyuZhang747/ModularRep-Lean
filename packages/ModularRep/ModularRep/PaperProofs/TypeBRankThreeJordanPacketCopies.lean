import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers
import ModularRep.IBrBlockEquivTransport
import ModularRep.IrreducibleBrauerCharacterEquiv

/-!
# Literal packets under the canonical Levi copy equivalence

The root, complete primitive decomposition and packet idempotent are all
transported through the same group equivalence. The existing block-index
transport theorem determines the supporting primitive block. Its literal
support equation and complete packet then transport through the same ring
equivalence, with no block or character compatibility input.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeJordanPacketCopies

open ModularRep FDRepSimpleClassKZero
open TypeBRankThreeJordanPacketCarriers

variable {k K G H I : Type}
variable [Field k] [Field K] [Group G] [Finite G] [Group H] [Finite H] [Fintype I]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {b : I → k[G]}
variable (root : PrimeRegularRootEmbedding 2 k K G)
variable (D : BlockIdempotentDecomposition b) (groupEquiv : G ≃* H)

/-- Canonical root injectivity makes the old block-index theorem apply
without a separately supplied character compatibility. -/
theorem blockIndex_alongMulEquiv (phi : IBr root) :
    blockIndex (root.alongMulEquiv groupEquiv) (D.alongMulEquiv groupEquiv)
        (IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv phi) =
      blockIndex root D phi :=
  irreducibleBrauerCharacterBlock_alongMulEquiv root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) groupEquiv
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (root.alongMulEquiv groupEquiv)) D phi

/-- The supporting primitive idempotent has the actual group algebra value
under this same map, rather than an independently chosen block label. -/
theorem supportingBlock_alongMulEquiv_val (phi : IBr root) :
    (supportingBlock (root.alongMulEquiv groupEquiv) (D.alongMulEquiv groupEquiv)
      (IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv phi)).val =
    MonoidAlgebra.mapDomainRingEquiv k groupEquiv (supportingBlock root D phi).val :=
  congrArg (fun i : I => MonoidAlgebra.mapDomainRingEquiv k groupEquiv (b i))
    (blockIndex_alongMulEquiv root D groupEquiv phi)

/-- The same index supports the original and transported algebra elements. -/
theorem blockSupport_alongMulEquiv_iff (eL : k[G]) (i : I) :
    ((D.alongMulEquiv groupEquiv).primitiveBlockOfIndex i).val *
        MonoidAlgebra.mapDomainRingEquiv k groupEquiv eL =
      ((D.alongMulEquiv groupEquiv).primitiveBlockOfIndex i).val ↔
    (D.primitiveBlockOfIndex i).val * eL = (D.primitiveBlockOfIndex i).val := by
  change MonoidAlgebra.mapDomainRingEquiv k groupEquiv (b i) *
      MonoidAlgebra.mapDomainRingEquiv k groupEquiv eL =
        MonoidAlgebra.mapDomainRingEquiv k groupEquiv (b i) ↔ b i * eL = b i
  rw [← map_mul]
  exact (MonoidAlgebra.mapDomainRingEquiv k groupEquiv).injective.eq_iff

/-- The copied supported-index set is computed from the original element. -/
theorem supportedIndexSet_alongMulEquiv (eL : k[G]) :
    {i : I | ((D.alongMulEquiv groupEquiv).primitiveBlockOfIndex i).val *
        MonoidAlgebra.mapDomainRingEquiv k groupEquiv eL =
      ((D.alongMulEquiv groupEquiv).primitiveBlockOfIndex i).val} =
    {i : I | (D.primitiveBlockOfIndex i).val * eL =
      (D.primitiveBlockOfIndex i).val} := by
  ext i
  exact blockSupport_alongMulEquiv_iff D groupEquiv eL i

/-- Packet membership follows from the literal supporting-block value map. -/
theorem inPacket_alongMulEquiv_iff (eL : k[G]) (phi : IBr root) :
    InPacket (root.alongMulEquiv groupEquiv) (D.alongMulEquiv groupEquiv)
        (MonoidAlgebra.mapDomainRingEquiv k groupEquiv eL)
        (IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv phi) ↔
      InPacket root D eL phi := by
  unfold InPacket
  rw [supportingBlock_alongMulEquiv_val root D groupEquiv phi, ← map_mul]
  exact (MonoidAlgebra.mapDomainRingEquiv k groupEquiv).injective.eq_iff

/-- The complete packet equivalence uses the original character map in
both directions; all support proofs are derived above. -/
def packetEquiv (eL : k[G]) :
    Packet root D eL ≃
      Packet (root.alongMulEquiv groupEquiv) (D.alongMulEquiv groupEquiv)
        (MonoidAlgebra.mapDomainRingEquiv k groupEquiv eL) where
  toFun phi := ⟨IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv phi.val,
    (inPacket_alongMulEquiv_iff root D groupEquiv eL phi.val).mpr phi.property⟩
  invFun psi := ⟨(IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv).symm psi.val,
    by
      apply (inPacket_alongMulEquiv_iff root D groupEquiv eL _).mp
      simpa only [Equiv.apply_symm_apply] using psi.property⟩
  left_inv phi := Subtype.ext
    ((IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv).symm_apply_apply phi.val)
  right_inv psi := Subtype.ext
    ((IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv).apply_symm_apply psi.val)

@[simp] theorem packetEquiv_val (eL : k[G]) (phi : Packet root D eL) :
    (packetEquiv root D groupEquiv eL phi).val =
      IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv phi.val := rfl

@[simp] theorem packetEquiv_symm_val (eL : k[G])
    (psi : Packet (root.alongMulEquiv groupEquiv) (D.alongMulEquiv groupEquiv)
      (MonoidAlgebra.mapDomainRingEquiv k groupEquiv eL)) :
    ((packetEquiv root D groupEquiv eL).symm psi).val =
      (IrreducibleBrauerCharacter.equivAlongMulEquiv root groupEquiv).symm psi.val := rfl

end ModularRep.PaperProofs.TypeBRankThreeJordanPacketCopies


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
