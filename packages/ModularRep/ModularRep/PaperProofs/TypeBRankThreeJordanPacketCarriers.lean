import ModularRep.IBrBlockAutomorphism
import ModularRep.CentralIdempotentBlockExpansion
import ModularRep.CyclicOuterBrauerExtension

/-!
Literal modular packets selected by a central idempotent.

The block supporting each character is obtained from the complete primitive
block decomposition and the canonical injectivity theorem for the same root.
No labelled subset of characters or blocks is supplied. Centrality and
idempotence are explicit hypotheses of the support and expansion statements.
The actor construction uses only invariance of the actual algebra element.
-/

noncomputable section

open scoped MonoidAlgebra BigOperators

namespace ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers

open ModularRep FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete

variable {k K G I : Type}
variable [Field k] [Field K] [Group G] [Finite G] [Fintype I]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {b : I → k[G]}

/-- The supporting index uses the injectivity derived from this root. -/
abbrev blockIndex (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (phi : IBr iota) : I :=
  irreducibleBrauerCharacterBlock iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) D phi

/-- The actual primitive central idempotent supporting the character. -/
def supportingBlock (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (phi : IBr iota) :
    LiteralPrimitiveBlock k G :=
  D.primitiveBlockOfIndex (blockIndex iota D phi)

@[simp]
theorem supportingBlock_val (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (phi : IBr iota) :
    (supportingBlock iota D phi).val = b (blockIndex iota D phi) :=
  rfl

/-- Literal support in the specified algebra element. -/
def InPacket (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) (phi : IBr iota) : Prop :=
  (supportingBlock iota D phi).val * e = (supportingBlock iota D phi).val

/-- The complete Brauer-character packet, with its original values. -/
def Packet (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) :=
  {phi : IBr iota // InPacket iota D e phi}

/-- The supported indices in the given complete decomposition. -/
def BlockSupport (D : BlockIdempotentDecomposition b) (e : k[G]) :=
  {i : I // (D.primitiveBlockOfIndex i).val * e =
    (D.primitiveBlockOfIndex i).val}

/-- All supported literal primitive central idempotents. -/
def LiteralSupport (e : k[G]) :=
  {c : LiteralPrimitiveBlock k G // c.val * e = c.val}

/-- Completeness identifies the supported indices with every literal
primitive block contained in the specified central idempotent. -/
def primitiveSupportEquiv (D : BlockIdempotentDecomposition b) (e : k[G]) :
    BlockSupport D e ≃ LiteralSupport e where
  toFun i := ⟨D.primitiveBlockOfIndex i.val, i.property⟩
  invFun c := ⟨D.primitiveBlockEquiv.symm c.val, by
    have hval : b (D.primitiveBlockEquiv.symm c.val) = c.val.val := by
      simpa only [BlockIdempotentDecomposition.primitiveBlockEquiv_apply,
        BlockIdempotentDecomposition.primitiveBlockOfIndex_val] using
        congrArg Subtype.val (D.primitiveBlockEquiv.apply_symm_apply c.val)
    change b (D.primitiveBlockEquiv.symm c.val) * e =
      b (D.primitiveBlockEquiv.symm c.val)
    rw [hval]
    exact c.property⟩
  left_inv i := by
    apply Subtype.ext
    exact D.primitiveBlockEquiv.symm_apply_apply i.val
  right_inv c := by
    apply Subtype.ext
    exact D.primitiveBlockEquiv.apply_symm_apply c.val

@[simp]
theorem primitiveSupportEquiv_val (D : BlockIdempotentDecomposition b)
    (e : k[G]) (i : BlockSupport D e) :
    (primitiveSupportEquiv D e i).val.val = b i.val :=
  rfl

/-- A primitive block is supported nontrivially exactly when it is fixed
by the given central idempotent. -/
theorem blockSupport_iff_nonzero (D : BlockIdempotentDecomposition b)
    (e : k[G]) (heIdempotent : IsIdempotentElem e)
    (heCentral : IsMulCentral e) (i : I) :
    b i * e = b i ↔ b i * e ≠ 0 :=
  (D.complete.mem_centralIdempotentSupport_iff_mul_eq_self
    D.primitive heIdempotent heCentral i).symm.trans
      (D.complete.mem_centralIdempotentSupport e i)

/-- The packet definition agrees with nonzero primitive support. -/
theorem inPacket_iff_nonzero (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G])
    (heIdempotent : IsIdempotentElem e) (heCentral : IsMulCentral e)
    (phi : IBr iota) :
    InPacket iota D e phi ↔ (supportingBlock iota D phi).val * e ≠ 0 :=
  blockSupport_iff_nonzero D e heIdempotent heCentral (blockIndex iota D phi)

/-- The same central idempotent is exactly the sum of its supported
primitive family members. -/
theorem supportedBlocks_sum (D : BlockIdempotentDecomposition b)
    (e : k[G]) (heIdempotent : IsIdempotentElem e)
    (heCentral : IsMulCentral e) :
    (∑ i ∈ D.complete.centralIdempotentSupport e, b i) = e :=
  D.complete.sum_centralIdempotentSupport_eq D.primitive heIdempotent heCentral

/-- The disjoint union uses the actual supporting blocks and the same root. -/
abbrev BlockUnion (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) :=
  Σ i : BlockSupport D e,
    IBrBlock iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      D i.val

/-- Every packet character belongs to its unique supported block, and
all characters of every supported block occur in the packet. -/
def packetEquivBlockUnion (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) :
    Packet iota D e ≃ BlockUnion iota D e where
  toFun phi := ⟨⟨blockIndex iota D phi.val, phi.property⟩, ⟨phi.val, rfl⟩⟩
  invFun x := ⟨x.2.val, by
    change b (blockIndex iota D x.2.val) * e = b (blockIndex iota D x.2.val)
    have hindex : blockIndex iota D x.2.val = x.1.val := x.2.property
    exact Eq.mpr (congrArg (fun i : I => b i * e = b i) hindex) x.1.property⟩
  left_inv phi := by
    apply Subtype.ext
    rfl
  right_inv x := by
    rcases x with ⟨⟨i, hi⟩, ⟨phi, hphi⟩⟩
    cases hphi
    rfl

@[simp]
theorem packetEquivBlockUnion_character
    (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) (phi : Packet iota D e) :
    (packetEquivBlockUnion iota D e phi).2.val = phi.val :=
  rfl

@[simp]
theorem packetEquivBlockUnion_symm_character
    (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) (x : BlockUnion iota D e) :
    ((packetEquivBlockUnion iota D e).symm x).val = x.2.val :=
  rfl

/-- The literal support covariance is inherited from the existing block
transport theorem, with no independent injectivity premise. -/
theorem supportingBlock_op_smul (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b)
    (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota) :
    supportingBlock iota D (a • phi) = a • supportingBlock iota D phi :=
  primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) D a phi

variable {E : Type} [Group E]

/-- Inverse pullback of characters transports their block by the forward
map on the group algebra basis. -/
theorem supportingBlock_smul_val (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (rho : E →* MulAut G)
    (a : E) (phi : IBr iota) :
    letI : MulAction E (IBr iota) := rightAutomorphismAction rho
    (supportingBlock iota D (a • phi)).val =
      MonoidAlgebra.mapDomainRingEquiv k (rho a)
        (supportingBlock iota D phi).val := by
  letI : MulAction E (IBr iota) := rightAutomorphismAction rho
  change (supportingBlock iota D (MulOpposite.op (rho a⁻¹) • phi)).val = _
  rw [supportingBlock_op_smul]
  change MonoidAlgebra.mapDomainRingEquiv k (rho a⁻¹).symm
      (supportingBlock iota D phi).val = _
  have hinverse : (rho a⁻¹).symm = rho a := by
    change (rho a⁻¹)⁻¹ = rho a
    rw [map_inv, inv_inv]
  rw [hinverse]

/-- Invariance of the actual algebra element implies packet preservation
for the existing right automorphism action. -/
theorem inPacket_smul (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) (rho : E →* MulAut G)
    (he : ∀ a : E, MonoidAlgebra.mapDomainRingEquiv k (rho a) e = e)
    (a : E) (phi : IBr iota) (hphi : InPacket iota D e phi) :
    letI : MulAction E (IBr iota) := rightAutomorphismAction rho
    InPacket iota D e (a • phi) := by
  letI : MulAction E (IBr iota) := rightAutomorphismAction rho
  change (supportingBlock iota D (a • phi)).val * e =
    (supportingBlock iota D (a • phi)).val
  rw [supportingBlock_smul_val iota D rho a phi]
  change (supportingBlock iota D phi).val * e =
    (supportingBlock iota D phi).val at hphi
  simpa only [map_mul, he a] using
    congrArg (MonoidAlgebra.mapDomainRingEquiv k (rho a)) hphi

/-- The invariant packet carries the restriction of the actual actor. -/
@[instance_reducible]
def packetMulAction (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) (rho : E →* MulAut G)
    (he : ∀ a : E, MonoidAlgebra.mapDomainRingEquiv k (rho a) e = e) :
    MulAction E (Packet iota D e) := by
  letI : MulAction E (IBr iota) := rightAutomorphismAction rho
  exact {
    smul := fun a phi => ⟨a • phi.val,
      inPacket_smul iota D e rho he a phi.val phi.property⟩
    one_smul := fun phi => Subtype.ext (one_smul E phi.val)
    mul_smul := fun a c phi => Subtype.ext (mul_smul a c phi.val) }

/-- The packet action has exactly the original irreducible character. -/
theorem packet_smul_val (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) (rho : E →* MulAut G)
    (he : ∀ a : E, MonoidAlgebra.mapDomainRingEquiv k (rho a) e = e)
    (a : E) (phi : Packet iota D e) :
    letI : MulAction E (IBr iota) := rightAutomorphismAction rho
    letI : MulAction E (Packet iota D e) := packetMulAction iota D e rho he
    (a • phi).val = a • phi.val :=
  rfl

/-- On prime regular elements, the action is the same inverse pullback. -/
theorem packet_smul_value (iota : PrimeRegularRootEmbedding 2 k K G)
    (D : BlockIdempotentDecomposition b) (e : k[G]) (rho : E →* MulAut G)
    (he : ∀ a : E, MonoidAlgebra.mapDomainRingEquiv k (rho a) e = e)
    (a : E) (phi : Packet iota D e) (g : PrimeRegularElement (G := G) 2) :
    letI : MulAction E (Packet iota D e) := packetMulAction iota D e rho he
    (a • phi).val.val g = phi.val.val (PrimeRegularElement.map (rho a⁻¹).toMonoidHom g) :=
  rfl

end ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
