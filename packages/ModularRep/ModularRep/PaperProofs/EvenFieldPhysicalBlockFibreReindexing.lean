import ModularRep.PaperProofs.EvenFieldBlockGroupEquivCoordinates

/-!
# Actual specified block reindexing and both independent block fibres

The label equivalence is computed from the two complete primitive catalogues
and the actual group equivalence. The Brauer map is the actual root-transport
map. The weight map is the whole-pair group-equivalence map, restricted to
the TWO supplied block sources. Only individual ambient catalogue equations
and the own-normalizer primitive equation enter the weight argument.

No fibre equivalence, ambient raw-block equation, selected-pair equality,
root compatibility, relation-forward law or completed target is a source
field. Independently selected representatives and their EVERY-root tuple
comparison remain separate from these computed carrier maps.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldPhysicalBlockFibreReindexing

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37Concrete
open EvenFieldBlockGroupEquivCoordinates
open OddTwoGroupEquivWeightBlocks

universe u

section Labels

variable {k G H B C : Type u} [Field k] [Group G] [Group H]
variable [Fintype B] [Fintype C]
variable {bG : B → k[G]} {bH : C → k[H]}
variable (DG : BlockIdempotentDecomposition bG)
variable (DH : BlockIdempotentDecomposition bH) (e : G ≃* H)

/-- Each complete catalogue indexes the same literal target primitive blocks.
No matching of block labels is supplied independently. -/
def blockLabelEquiv : B ≃ C :=
  (DG.alongMulEquiv e).primitiveBlockEquiv.trans DH.primitiveBlockEquiv.symm

/-- The defining coordinate equation is a consequence of the actual label map. -/
theorem blockLabelEquiv_primitive (b : B) :
    bH (blockLabelEquiv DG DH e b) = MonoidAlgebra.domCongr k k e (bG b) := by
  have h := DH.primitiveBlockEquiv.apply_symm_apply
    ((DG.alongMulEquiv e).primitiveBlockEquiv b)
  exact congrArg Subtype.val h

/-- A selected target label is the computed one precisely when its specified
primitive is the actual image. No selected fibre is needed to choose it. -/
theorem blockLabelEquiv_eq_iff (b : B) (c : C) :
    blockLabelEquiv DG DH e b = c ↔
      bH c = MonoidAlgebra.domCongr k k e (bG b) := by
  constructor
  · intro h
    rw [← h]
    exact blockLabelEquiv_primitive DG DH e b
  · intro h
    apply DH.primitiveBlockOfIndex_injective
    apply Subtype.ext
    exact (blockLabelEquiv_primitive DG DH e b).trans h.symm

variable [MulAction (MulAut G)ᵐᵒᵖ B] [MulAction (MulAut H)ᵐᵒᵖ C]
variable (actionG : PhysicalBlockAction bG) (actionH : PhysicalBlockAction bH)

include actionG actionH in
/-- Naturality holds for all specified labels, not only fixed labels. -/
theorem blockLabelEquiv_smul (a : (MulAut G)ᵐᵒᵖ) (b : B) :
    blockLabelEquiv DG DH e (a • b) =
      oppositeAutEquiv e a • blockLabelEquiv DG DH e b := by
  apply idempotent_injective DH
  rw [blockLabelEquiv_primitive DG DH e (a • b),
    actionH (oppositeAutEquiv e a) (blockLabelEquiv DG DH e b),
    blockLabelEquiv_primitive DG DH e b, actionG a b]
  exact basisMap_intertwines e a (bG b)

/-- The full block stabilizer comparison now uses the computed label match. -/
def stabilizerEquiv (b : B) :
    MulAction.stabilizer (MulAut G)ᵐᵒᵖ b ≃*
      MulAction.stabilizer (MulAut H)ᵐᵒᵖ (blockLabelEquiv DG DH e b) :=
  blockStabilizerEquiv DG DH e actionG actionH b (blockLabelEquiv DG DH e b)
    (blockLabelEquiv_primitive DG DH e b)

@[simp] theorem stabilizerEquiv_coe (b : B)
    (a : MulAction.stabilizer (MulAut G)ᵐᵒᵖ b) :
    (stabilizerEquiv DG DH e actionG actionH b a).1 = oppositeAutEquiv e a.1 := rfl

section Presentations

variable {Gamma Delta : Type u} [Group Gamma] [Group Delta]
variable (b : B) (gamma : Gamma →* MulAut G) (delta : Delta →* MulAut H)
variable (sG : Gamma ≃* MulAction.stabilizer (MulAut G)ᵐᵒᵖ b)
variable (sH : Delta ≃* MulAction.stabilizer (MulAut H)ᵐᵒᵖ
  (blockLabelEquiv DG DH e b))

/-- Existing actual stabilizer presentations compose with the computed
specified-label comparison; they are not replaced by full Aut. -/
def presentationEquiv : Gamma ≃* Delta :=
  sG.trans ((stabilizerEquiv DG DH e actionG actionH b).trans sH.symm)

variable (sG_coe : ∀ a, (sG a).1 = inverseOpHom gamma a)
variable (sH_coe : ∀ a, (sH a).1 = inverseOpHom delta a)

include sG_coe sH_coe in
theorem presentationEquiv_inverseOp (a : Gamma) :
    inverseOpHom delta (presentationEquiv DG DH e actionG actionH b sG sH a) =
      oppositeAutEquiv e (inverseOpHom gamma a) :=
  gammaEquiv_inverseOp DG DH e actionG actionH b (blockLabelEquiv DG DH e b)
    (blockLabelEquiv_primitive DG DH e b) gamma delta sG sH sG_coe sH_coe a

include sG_coe sH_coe in
theorem presentationEquiv_gamma (a : Gamma) :
    delta (presentationEquiv DG DH e actionG actionH b sG sH a) =
      MulAut.congr e (gamma a) :=
  gammaEquiv_gamma DG DH e actionG actionH b (blockLabelEquiv DG DH e b)
    (blockLabelEquiv_primitive DG DH e b) gamma delta sG sH sG_coe sH_coe a

include sG_coe sH_coe in
theorem presentationEquiv_value (a : Gamma) (x : G) :
    delta (presentationEquiv DG DH e actionG actionH b sG sH a) (e x) =
      e (gamma a x) :=
  gammaEquiv_value DG DH e actionG actionH b (blockLabelEquiv DG DH e b)
    (blockLabelEquiv_primitive DG DH e b) gamma delta sG sH sG_coe sH_coe a x

end Presentations
end Labels

section Brauer

variable {p : ℕ} {k K G H B C : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H] [Fintype B] [Fintype C]

/-- Relabelling a complete specified decomposition changes only the label
of the same supporting simple module. -/
theorem brauerBlock_relabel
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {b : B → k[G]} {c : C → k[G]}
    (D : BlockIdempotentDecomposition b) (E : BlockIdempotentDecomposition c)
    (labels : B ≃ C) (primitive : ∀ x, c (labels x) = b x) (psi : IBr iota) :
    irreducibleBrauerCharacterBlock iota hinj E psi =
      labels (irreducibleBrauerCharacterBlock iota hinj D psi) := by
  let X := (simpleModuleClassEquivIBr iota hinj).symm psi
  letI : IsSimpleModule k[G] (Representation.asModule (simpleClassFDRep X).ρ) :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple X)
  change E.moduleBlock (V := Representation.asModule (simpleClassFDRep X).ρ) =
    labels (D.moduleBlock (V := Representation.asModule (simpleClassFDRep X).ρ))
  symm
  apply E.moduleBlock_eq_of_smul_eq_self
  intro v
  rw [primitive]
  exact D.moduleBlock_smul v

variable {bG : B → k[G]} {bH : C → k[H]}
variable (DG : BlockIdempotentDecomposition bG)
variable (DH : BlockIdempotentDecomposition bH) (e : G ≃* H)
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (hinjH : IrreducibleBrauerCharacterInjectivity (iota.alongMulEquiv e))

/-- The actual transported character belongs to the computed specified label. -/
theorem brauerBlock_map (psi : IBr iota) :
    irreducibleBrauerCharacterBlock (iota.alongMulEquiv e) hinjH DH
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi) =
      blockLabelEquiv DG DH e (irreducibleBrauerCharacterBlock iota hinj DG psi) := by
  rw [brauerBlock_relabel (iota.alongMulEquiv e) hinjH (DG.alongMulEquiv e) DH
    (blockLabelEquiv DG DH e) (blockLabelEquiv_primitive DG DH e)]
  exact congrArg (blockLabelEquiv DG DH e)
    (irreducibleBrauerCharacterBlock_alongMulEquiv iota hinj e hinjH DG psi)

/-- Restrict the existing actual IBr equivalence across DIFFERENT label types. -/
def brauerEquiv (b : B) :
    BrauerFibre iota hinj DG b ≃
      BrauerFibre (iota.alongMulEquiv e) hinjH DH (blockLabelEquiv DG DH e b) where
  toFun psi := ⟨IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi.1, by
    rw [brauerBlock_map DG DH e iota hinj hinjH, psi.2]⟩
  invFun psi := ⟨(IrreducibleBrauerCharacter.equivAlongMulEquiv iota e).symm psi.1, by
    apply (blockLabelEquiv DG DH e).injective
    rw [← brauerBlock_map DG DH e iota hinj hinjH, Equiv.apply_symm_apply]
    exact psi.2⟩
  left_inv psi := Subtype.ext
    ((IrreducibleBrauerCharacter.equivAlongMulEquiv iota e).symm_apply_apply psi.1)
  right_inv psi := Subtype.ext
    ((IrreducibleBrauerCharacter.equivAlongMulEquiv iota e).apply_symm_apply psi.1)

@[simp] theorem brauerEquiv_val (b : B) (psi : BrauerFibre iota hinj DG b) :
    (brauerEquiv DG DH e iota hinj hinjH b psi).1 =
      IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi.1 := rfl

theorem brauerEquiv_values (b : B) (psi : BrauerFibre iota hinj DG b)
    (x : PrimeRegularElement (G := H) p) :
    (brauerEquiv DG DH e iota hinj hinjH b psi).1.1 x =
      psi.1.1 (PrimeRegularElement.map e.symm.toMonoidHom x) := rfl

/-- The actual character action equation retains the full opposite automorphism. -/
theorem brauerEquiv_twist (b : B) (psi : BrauerFibre iota hinj DG b)
    (a : (MulAut G)ᵐᵒᵖ) :
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota e (a • psi.1) =
      oppositeAutEquiv e a • (brauerEquiv DG DH e iota hinj hinjH b psi).1 :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul iota e psi.1 a

end Brauer

section Weights

local instance reindexingSubgroupFintype {A : Type u}
    [Group A] [Finite A] (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

variable {p : ℕ} {k K G H B C : Type u}
variable [Field k] [Field K] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H] [Fintype B] [Fintype C]
variable {bG : B → k[G]} {bH : C → k[H]}
variable (DG : BlockIdempotentDecomposition bG)
variable (DH : BlockIdempotentDecomposition bH) (e : G ≃* H)
variable (OG : LocalBlockInductionOperations (p := p) (k := k) (K := K)
  (G := G) (Block := B))
variable (OH : LocalBlockInductionOperations (p := p) (k := k) (K := K)
  (G := H) (Block := C))
variable (ambientG : ∀ b, OG.ambientBlockData.blockIdempotent b = bG b)
variable (ambientH : ∀ c, OH.ambientBlockData.blockIdempotent c = bH c)
variable (ownPrimitive : ∀ W : CharacterWeight p K G,
  MonoidAlgebra.domCongr k k (normalizerEquiv e W.subgroup)
    (ownNormalizerBlock OG W).1 = (ownNormalizerBlock OH (W.mapGroupEquiv e)).1)

include ambientG ambientH in
/-- Ambient central characters follow from the computed label coordinates. -/
theorem ambientCentralCharacter_map (b : B) :
    centralCharacterAlongMulEquiv e (ambientCentralCharacter OG b) =
      ambientCentralCharacter OH (blockLabelEquiv DG DH e b) := by
  exact @centralCharacterAlongMulEquiv_eq_of_blockIdempotent k G H B C
    _ _ _ _ _ _ OG.ambientBlockData.fintypeBlock OH.ambientBlockData.fintypeBlock
    _ _ _ _ e OG.ambientBlockData.catalogue OH.ambientBlockData.catalogue
    b (blockLabelEquiv DG DH e b) (by
      apply Subtype.ext
      change MonoidAlgebra.domCongr k k e (OG.ambientBlockData.blockIdempotent b) =
        OH.ambientBlockData.blockIdempotent (blockLabelEquiv DG DH e b)
      rw [ambientG b, ambientH (blockLabelEquiv DG DH e b),
        blockLabelEquiv_primitive DG DH e b])

include ownPrimitive in
/-- Only the primitive of the actual OWN local character is compared. -/
theorem ownCentralCharacter_map (W : CharacterWeight p K G) :
    centralCharacterAlongMulEquiv (normalizerEquiv e W.subgroup)
        (ownCentralCharacter OG W) =
      ownCentralCharacter OH (W.mapGroupEquiv e) := by
  letI := (OG.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI := (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).fintypeBlock
  exact centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    (normalizerEquiv e W.subgroup)
    (OG.inflatedNormalizerBlockData W.subgroup).catalogue
    (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).catalogue (by
      apply Subtype.ext
      exact ownPrimitive W)

include ambientG ambientH ownPrimitive in
/-- Induction and uniqueness derive the actual ambient block, including its
computed new label. No ambient block map is an input. -/
theorem rawWeightBlock_map (W : CharacterWeight p K G) :
    OH.rawWeightBlock (W.mapGroupEquiv e) =
      blockLabelEquiv DG DH e (OG.rawWeightBlock W) := by
  let labels := blockLabelEquiv DG DH e
  have ambientTransport :=
    ambientCentralCharacter_map DG DH e OG OH ambientG ambientH (OG.rawWeightBlock W)
  change OH.rawWeightBlock (W.mapGroupEquiv e) = labels (OG.rawWeightBlock W)
  letI := OG.ambientBlockData.fintypeBlock
  letI := (OG.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI := (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).fintypeBlock
  have sourceInduction := inducedBlock_spec
    (Subgroup.normalizer (W.subgroup : Set G))
    (OG.inflatedNormalizerBlockData W.subgroup).catalogue
    OG.ambientBlockData.catalogue (ownNormalizerBlock OG W)
    (OG.blockInductionDefined W)
  have transported := @blockInducesTo_alongMulEquiv k G H
    _ _ _ _ _ _
    (Subgroup.normalizer (W.subgroup : Set G))
    (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H))
    _ B _ C
    (OG.inflatedNormalizerBlockData W.subgroup).fintypeBlock
    OG.ambientBlockData.fintypeBlock
    (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).fintypeBlock
    OH.ambientBlockData.fintypeBlock
    _ _ _ _ _ _ _ _
    e (normalizerEquiv e W.subgroup) (normalizer_inclusion_square e W)
    (OG.inflatedNormalizerBlockData W.subgroup).catalogue
    OG.ambientBlockData.catalogue
    (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).catalogue
    OH.ambientBlockData.catalogue
    (ownNormalizerBlock OG W) (OG.rawWeightBlock W)
    (ownNormalizerBlock OH (W.mapGroupEquiv e))
    (labels (OG.rawWeightBlock W))
    (ownCentralCharacter_map e OG OH ownPrimitive W)
    ambientTransport
    sourceInduction
  letI := OH.ambientBlockData.fintypeBlock
  have unique := eq_inducedBlock_of_blockInducesTo
    (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H))
    (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).catalogue
    OH.ambientBlockData.catalogue (ownNormalizerBlock OH (W.mapGroupEquiv e))
    (OH.blockInductionDefined (W.mapGroupEquiv e)) transported
  simpa only [LocalBlockInductionOperations.rawWeightBlock,
    LocalBlockInductionOperations.induceToAmbient, ownNormalizerBlock] using unique.symm

section BothSources

variable [MulAction (MulAut G)ᵐᵒᵖ B] [MulAction (MulAut H)ᵐᵒᵖ C]
variable (SG : LocalBlockInductionSource (p := p) (k := k) (K := K)
  (G := G) (Block := B))
variable (SH : LocalBlockInductionSource (p := p) (k := k) (K := K)
  (G := H) (Block := C))
variable (sourceAmbientG : ∀ b, SG.operations.ambientBlockData.blockIdempotent b = bG b)
variable (sourceAmbientH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = bH c)
variable (sourceOwnPrimitive : ∀ W : CharacterWeight p K G,
  MonoidAlgebra.domCongr k k (normalizerEquiv e W.subgroup)
    (ownNormalizerBlock SG.operations W).1 =
      (ownNormalizerBlock SH.operations (W.mapGroupEquiv e)).1)

include sourceAmbientG sourceAmbientH sourceOwnPrimitive in
/-- Both actual quotient descents retain the computed specified block label. -/
theorem weightBlock_map
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    SH.weightBlock (CharacterWeight.conjugacyClassGroupEquiv e w) =
      blockLabelEquiv DG DH e (SG.weightBlock w) := by
  refine Quotient.inductionOn w ?_
  intro x
  refine Quotient.inductionOn x ?_
  intro W
  exact rawWeightBlock_map DG DH e SG.operations SH.operations
    sourceAmbientG sourceAmbientH sourceOwnPrimitive W

/-- Restrict the actual whole-pair class map to the TWO independent sources;
the target action/source is not replaced by a newly transported copy. -/
def weightEquiv (b : B) : SG.Fibre b ≃ SH.Fibre (blockLabelEquiv DG DH e b) where
  toFun w := ⟨CharacterWeight.conjugacyClassGroupEquiv e w.1,
    (weightBlock_map DG DH e SG SH sourceAmbientG sourceAmbientH sourceOwnPrimitive w.1).trans
      (congrArg (blockLabelEquiv DG DH e) w.2)⟩
  invFun w := ⟨(CharacterWeight.conjugacyClassGroupEquiv e).symm w.1, by
    have h := weightBlock_map DG DH e SG SH sourceAmbientG sourceAmbientH sourceOwnPrimitive
      ((CharacterWeight.conjugacyClassGroupEquiv e).symm w.1)
    rw [Equiv.apply_symm_apply] at h
    apply (blockLabelEquiv DG DH e).injective
    exact h.symm.trans w.2⟩
  left_inv w := Subtype.ext ((CharacterWeight.conjugacyClassGroupEquiv e).symm_apply_apply w.1)
  right_inv w := Subtype.ext ((CharacterWeight.conjugacyClassGroupEquiv e).apply_symm_apply w.1)

@[simp] theorem weightEquiv_val (b : B) (w : SG.Fibre b) :
    (weightEquiv DG DH e SG SH sourceAmbientG sourceAmbientH sourceOwnPrimitive b w).1 =
      CharacterWeight.conjugacyClassGroupEquiv e w.1 := rfl

theorem weightEquiv_twist (b : B) (w : SG.Fibre b) (a : (MulAut G)ᵐᵒᵖ) :
    CharacterWeight.conjugacyClassGroupEquiv e (a • w.1) =
      oppositeAutEquiv e a •
        (weightEquiv DG DH e SG SH sourceAmbientG sourceAmbientH sourceOwnPrimitive b w).1 :=
  CharacterWeight.conjugacyClassGroupEquiv_op_smul e a w.1

end BothSources
end Weights

end ModularRep.PaperProofs.EvenFieldPhysicalBlockFibreReindexing


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
