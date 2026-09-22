import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.PaperProofs.OddTwoGroupEquivBrauerBlocks
import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks

/-!
# Specified block stabilizers under an actual group equivalence

The two block-label types may differ. A selected block is matched only by
its actual primitive idempotent under the group algebra map. The individual
block actions have their usual primitive-idempotent value laws. K derives
the equivalence of the FULL block stabilizers and, for actual stabilizer
presentations, the precise gamma square. No principal-block fixedness or
full-Aut replacement is used.

The last section retains the existing computed Brauer and whole-weight
fibre maps on common specified labels and proves their actual action
equations. Independently selected representatives, their selected quotient
reductions, EVERY compatible own-normalizer root and standard relations
are not transported by this module.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldBlockGroupEquivCoordinates

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37Concrete
open OddTwoGroupEquivWeightBlocks

universe u

section Automorphisms

variable {G H : Type u} [Group G] [Group H] (e : G ≃* H)

/-- Conjugate the actual automorphism and retain the opposite convention. -/
def oppositeAutEquiv : (MulAut G)ᵐᵒᵖ ≃* (MulAut H)ᵐᵒᵖ where
  toFun a := MulOpposite.op (MulAut.congr e a.unop)
  invFun a := MulOpposite.op (MulAut.congr e.symm a.unop)
  left_inv a := by
    apply MulOpposite.unop_injective
    ext x
    change e.symm (e (a.unop (e.symm (e x)))) = a.unop x
    simp only [MulEquiv.symm_apply_apply]
  right_inv a := by
    apply MulOpposite.unop_injective
    ext x
    change e (e.symm (a.unop (e (e.symm x)))) = a.unop x
    simp only [MulEquiv.apply_symm_apply]
  map_mul' a b := by
    change MulOpposite.op (MulAut.congr e (b.unop * a.unop)) =
      MulOpposite.op (MulAut.congr e a.unop) *
        MulOpposite.op (MulAut.congr e b.unop)
    exact congrArg MulOpposite.op (map_mul (MulAut.congr e) b.unop a.unop)

@[simp] theorem oppositeAutEquiv_apply (a : (MulAut G)ᵐᵒᵖ) :
    oppositeAutEquiv e a = MulOpposite.op (MulAut.congr e a.unop) := rfl

/-- The square is equality on every actual group element. -/
theorem oppositeAutEquiv_value (a : (MulAut G)ᵐᵒᵖ) (x : G) :
    (oppositeAutEquiv e a).unop (e x) = e (a.unop x) := by
  change e (a.unop (e.symm (e x))) = e (a.unop x)
  rw [MulEquiv.symm_apply_apply]

end Automorphisms

section PhysicalBlocks

variable {k G H B C : Type u} [Field k] [Group G] [Group H]
variable [Fintype B] [Fintype C]
variable [MulAction (MulAut G)ᵐᵒᵖ B] [MulAction (MulAut H)ᵐᵒᵖ C]
variable {bG : B → k[G]} {bH : C → k[H]}
variable (DG : BlockIdempotentDecomposition bG)
variable (DH : BlockIdempotentDecomposition bH) (e : G ≃* H)

/-- The value law for a labelled specified block action, separately on each
group. It asserts no comparison, fixedness or chosen stabilizer. -/
def PhysicalBlockAction {X I : Type u} [Group X] [MulAction (MulAut X)ᵐᵒᵖ I]
    (idempotent : I → k[X]) : Prop :=
  ∀ (a : (MulAut X)ᵐᵒᵖ) (b : I),
    idempotent (a • b) = MonoidAlgebra.domCongr k k a.unop.symm (idempotent b)

/-- The canonical action on literal primitive blocks has this value law
definitionally; labelled catalogues only need their standard interpretation. -/
theorem literalPhysicalBlockAction {X : Type u} [Group X] :
    PhysicalBlockAction (fun b : LiteralPrimitiveBlock k X => b.1) := by
  intro a b
  rfl

include DG in
/-- The primitive catalogue makes its actual idempotent map injective. -/
theorem idempotent_injective : Function.Injective bG := by
  intro b c h
  apply DG.primitiveBlockOfIndex_injective
  exact Subtype.ext h

/-- Basis transport intertwines the two inverse automorphisms. -/
theorem basisMap_intertwines (a : (MulAut G)ᵐᵒᵖ) (z : k[G]) :
    MonoidAlgebra.domCongr k k e
        (MonoidAlgebra.domCongr k k a.unop.symm z) =
      MonoidAlgebra.domCongr k k (MulAut.congr e a.unop).symm
        (MonoidAlgebra.domCongr k k e z) := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  simp only [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm]
  change z.coeff (a.unop (e.symm x)) =
    z.coeff (e.symm (e (a.unop (e.symm x))))
  rw [MulEquiv.symm_apply_apply]

variable (actionG : PhysicalBlockAction bG) (actionH : PhysicalBlockAction bH)
variable (b : B) (c : C)
variable (primitive : bH c = MonoidAlgebra.domCongr k k e (bG b))

include DG DH actionG actionH primitive in
/-- Full block fixedness corresponds under the actual group map. The two
block-label types need not agree, and the block need not be principal. -/
theorem block_fixed_iff (a : (MulAut G)ᵐᵒᵖ) :
    a • b = b ↔ oppositeAutEquiv e a • c = c := by
  have h : bH (oppositeAutEquiv e a • c) =
      MonoidAlgebra.domCongr k k e (bG (a • b)) := by
    rw [actionH, primitive, actionG]
    exact (basisMap_intertwines e a (bG b)).symm
  constructor
  · intro ha
    apply idempotent_injective DH
    rw [h, ha, primitive]
  · intro ha
    apply idempotent_injective DG
    apply (MonoidAlgebra.domCongr k k e).injective
    rw [← h, ha, primitive]

/-- Restrict conjugation of actual automorphisms to the FULL two block
stabilizers, using only the proved specified-block comparison. -/
def blockStabilizerEquiv :
    MulAction.stabilizer (MulAut G)ᵐᵒᵖ b ≃*
      MulAction.stabilizer (MulAut H)ᵐᵒᵖ c where
  toFun a := ⟨oppositeAutEquiv e a.1,
    (block_fixed_iff DG DH e actionG actionH b c primitive a.1).mp a.2⟩
  invFun a := ⟨(oppositeAutEquiv e).symm a.1, by
    apply (block_fixed_iff DG DH e actionG actionH b c primitive _).mpr
    rw [MulEquiv.apply_symm_apply]
    exact a.2⟩
  left_inv a := by
    apply Subtype.ext
    exact (oppositeAutEquiv e).symm_apply_apply a.1
  right_inv a := by
    apply Subtype.ext
    exact (oppositeAutEquiv e).apply_symm_apply a.1
  map_mul' a d := Subtype.ext ((oppositeAutEquiv e).map_mul a.1 d.1)

@[simp] theorem blockStabilizerEquiv_coe
    (a : MulAction.stabilizer (MulAut G)ᵐᵒᵖ b) :
    (blockStabilizerEquiv DG DH e actionG actionH b c primitive a).1 =
      oppositeAutEquiv e a.1 := rfl

section Presentations

variable {Gamma Delta : Type u} [Group Gamma] [Group Delta]
variable (gamma : Gamma →* MulAut G) (delta : Delta →* MulAut H)
variable (sG : Gamma ≃* MulAction.stabilizer (MulAut G)ᵐᵒᵖ b)
variable (sH : Delta ≃* MulAction.stabilizer (MulAut H)ᵐᵒᵖ c)
variable (sG_coe : ∀ a, (sG a).1 = inverseOpHom gamma a)
variable (sH_coe : ∀ a, (sH a).1 = inverseOpHom delta a)

/-- The inputs sG/sH are the actual Definition 3.5 stabilizer adapters'
equivalences. No faithfulness/surjectivity conclusion is added as a source. -/
def gammaEquiv : Gamma ≃* Delta :=
  sG.trans ((blockStabilizerEquiv DG DH e actionG actionH b c primitive).trans sH.symm)

include sG_coe sH_coe in
theorem gammaEquiv_inverseOp (a : Gamma) :
    inverseOpHom delta
        (gammaEquiv DG DH e actionG actionH b c primitive sG sH a) =
      oppositeAutEquiv e (inverseOpHom gamma a) := by
  rw [← sH_coe]
  change (sH (sH.symm
    (blockStabilizerEquiv DG DH e actionG actionH b c primitive (sG a)))).1 = _
  rw [MulEquiv.apply_symm_apply, blockStabilizerEquiv_coe, sG_coe]

include sG_coe sH_coe in
/-- The gamma comparison formerly left unconsumed in the high-rank packet
is now a consequence of the actual stabilizer maps. -/
theorem gammaEquiv_gamma (a : Gamma) :
    delta (gammaEquiv DG DH e actionG actionH b c primitive sG sH a) =
      MulAut.congr e (gamma a) := by
  have h := gammaEquiv_inverseOp DG DH e actionG actionH b c primitive
    gamma delta sG sH sG_coe sH_coe a
  change MulOpposite.op (delta
      (gammaEquiv DG DH e actionG actionH b c primitive sG sH a)⁻¹) =
    MulOpposite.op (MulAut.congr e (gamma a⁻¹)) at h
  simp only [map_inv] at h
  exact inv_injective (MulOpposite.op_injective h)

include sG_coe sH_coe in
theorem gammaEquiv_value (a : Gamma) (x : G) :
    delta (gammaEquiv DG DH e actionG actionH b c primitive sG sH a) (e x) =
      e (gamma a x) := by
  rw [gammaEquiv_gamma DG DH e actionG actionH b c primitive
    gamma delta sG sH sG_coe sH_coe]
  change e (gamma a (e.symm (e x))) = e (gamma a x)
  rw [MulEquiv.symm_apply_apply]

end Presentations
end PhysicalBlocks

section ActualFibres

variable {p : ℕ} {k K G H Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H] [Fintype Block]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota) (e : G ≃* H)
variable (hinjH : IrreducibleBrauerCharacterInjectivity (iota.alongMulEquiv e))
variable {idempotent : Block → k[G]} (D : BlockIdempotentDecomposition idempotent)
variable (A : AmbientBlockCatalogueData (k := k) (G := H) (Block := Block))
variable (primitive : ∀ b, A.blockIdempotent b =
  MonoidAlgebra.domCongr k k e (idempotent b))

/-- The existing specified-catalogue consumer supplies the Brauer fibre map;
no independent equivalence or independently chosen target root is accepted. -/
def brauerFibreEquiv (b : Block) :=
  OddTwoGroupEquivBrauerBlocks.brauerFibreEquiv iota hinj e hinjH D A primitive b

/-- Actual global action naturality of the computed fibre values. This
retains the raw group automorphism, prior to any Gamma presentation. -/
theorem brauerFibreEquiv_twist (b : Block) (psi : BrauerFibre iota hinj D b)
    (a : (MulAut G)ᵐᵒᵖ) :
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota e (a • psi.1) =
      oppositeAutEquiv e a • (brauerFibreEquiv iota hinj e hinjH D A primitive b psi).1 :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul iota e psi.1 a

variable [MulAction (MulAut G)ᵐᵒᵖ Block]
variable (S : LocalBlockInductionSource (p := p) (k := k) (K := K)
  (G := G) (Block := Block))
variable (O : LocalBlockInductionOperations (p := p) (k := k) (K := K)
  (G := H) (Block := Block))
variable (dictionary : PrimitiveDictionary S.operations O e)

/-- The target weight source is the existing computed source on the exact
operations and pulled-back block action, with the own primitive dictionary. -/
def weightFibreEquiv (b : Block) := fibreEquiv O e S dictionary b

/-- The actual whole-pair class map, not a separate selected-class map,
supplies the weight fibre's automorphism equation. -/
theorem weightFibreEquiv_twist (b : Block) (w : S.Fibre b)
    (a : (MulAut G)ᵐᵒᵖ) :
    CharacterWeight.conjugacyClassGroupEquiv e (a • w.1) =
      oppositeAutEquiv e a • (weightFibreEquiv e S O dictionary b w).1 :=
  CharacterWeight.conjugacyClassGroupEquiv_op_smul e a w.1

end ActualFibres

end ModularRep.PaperProofs.EvenFieldBlockGroupEquivCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
