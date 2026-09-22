import ModularRep.PaperProofs.OddTwoWeightGroupEquiv
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.CentralCharacterCovering

/-!
# Actual block transport for group-equivalent weights

The only dictionary equations concern the SAME ambient primitive labels
and the OWN normalizer primitive block under the canonical group algebra
maps. Central character transport and uniqueness of induced blocks derive
raw block equality. The actual pulled-back block action then derives the
target source laws and the equivalence of existing block fibres.

No ambient raw-block equality, fibre equivalence, root equality, selected
relation, completed seed, or iBAW conclusion is a dictionary field.
-/

noncomputable section

open scoped MonoidAlgebra
open ModularRep ModularRep.CharacterWeight

namespace ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks

universe u

variable {p : ℕ} {k K G H Block : Type u}
variable [Field k] [Field K] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

local instance groupEquivBlockSubgroupFintype {A : Type u}
    [Group A] [Finite A] (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

/-- The actual composite local-character block and quotient inflation. -/
def ownNormalizerBlock
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K)
      (G := G) (Block := Block)) (W : CharacterWeight p K G) :
    InflatedNormalizerBlock (k := k) W.subgroup :=
  O.inflateToNormalizer W.subgroup
    (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

/-- A narrow coordinate dictionary indexed by the EXACT two operations.
It contains only actual primitive-idempotent equations. Its source
interpretation must authenticate these operations under the same modular
system; it is not automatically inhabited for arbitrary operations. -/
structure PrimitiveDictionary
    (OG : LocalBlockInductionOperations (p := p) (k := k) (K := K)
      (G := G) (Block := Block))
    (OH : LocalBlockInductionOperations (p := p) (k := k) (K := K)
      (G := H) (Block := Block)) (e : G ≃* H) : Prop where
  ambient_primitive :
    letI := OG.isAlgClosed
    ∀ b : Block,
      MonoidAlgebra.domCongr k k e (OG.ambientBlockData.blockIdempotent b) =
        OH.ambientBlockData.blockIdempotent b
  normalizer_primitive : ∀ W : CharacterWeight p K G,
    MonoidAlgebra.domCongr k k (normalizerEquiv e W.subgroup)
      (ownNormalizerBlock OG W).1 =
        (ownNormalizerBlock OH (W.mapGroupEquiv e)).1

/-- Retain the finite block index stored in the exact ambient catalogue. -/
def ambientCentralCharacter
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K)
      (G := G) (Block := Block)) (b : Block) : GroupAlgebraCenter k G →ₐ[k] k :=
  letI := O.isAlgClosed
  letI := O.ambientBlockData.fintypeBlock
  O.ambientBlockData.catalogue.centralCharacter b

/-- The central character of the own inflated primitive normalizer block. -/
def ownCentralCharacter
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K)
      (G := G) (Block := Block)) (W : CharacterWeight p K G) :
    GroupAlgebraCenter k (Subgroup.normalizer (W.subgroup : Set G)) →ₐ[k] k :=
  letI := O.isAlgClosed
  letI := (O.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  (O.inflatedNormalizerBlockData W.subgroup).catalogue.centralCharacter
    (ownNormalizerBlock O W)

variable
    (OG : LocalBlockInductionOperations (p := p) (k := k) (K := K)
      (G := G) (Block := Block))
    (OH : LocalBlockInductionOperations (p := p) (k := k) (K := K)
      (G := H) (Block := Block))
    (e : G ≃* H) (dictionary : PrimitiveDictionary OG OH e)

include dictionary in
/-- Ambient central characters are consequences of primitive matching. -/
theorem ambientCentralCharacter_transport (b : Block) :
    centralCharacterAlongMulEquiv e (ambientCentralCharacter OG b) =
      ambientCentralCharacter OH b := by
  letI := OG.isAlgClosed
  letI := OG.ambientBlockData.fintypeBlock
  exact @centralCharacterAlongMulEquiv_eq_of_blockIdempotent k G H Block Block
    _ OG.isAlgClosed _ _ _ _
    OG.ambientBlockData.fintypeBlock OH.ambientBlockData.fintypeBlock
    _ _ _ _ e OG.ambientBlockData.catalogue OH.ambientBlockData.catalogue b b (by
      apply Subtype.ext
      exact dictionary.ambient_primitive b)

include dictionary in
/-- The own ordinary character determines the local block used here. -/
theorem ownCentralCharacter_transport (W : CharacterWeight p K G) :
    centralCharacterAlongMulEquiv (normalizerEquiv e W.subgroup)
        (ownCentralCharacter OG W) =
      ownCentralCharacter OH (W.mapGroupEquiv e) := by
  letI := OG.isAlgClosed
  letI := (OG.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI := (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).fintypeBlock
  exact centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    (normalizerEquiv e W.subgroup)
    (OG.inflatedNormalizerBlockData W.subgroup).catalogue
    (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).catalogue (by
      apply Subtype.ext
      exact dictionary.normalizer_primitive W)

/-- The normalizer inclusion square uses the original e on every element. -/
theorem normalizer_inclusion_square (W : CharacterWeight p K G) :
    e.toMonoidHom.comp (Subgroup.normalizer (W.subgroup : Set G)).subtype =
      (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)).subtype.comp
        (normalizerEquiv e W.subgroup).toMonoidHom := by
  ext x
  rfl

include dictionary in
/-- Primitive transport implies preservation of the K-selected ambient
block. No raw block or principal membership is supplied as a premise. -/
theorem rawWeightBlock_eq (W : CharacterWeight p K G) :
    OH.rawWeightBlock (W.mapGroupEquiv e) = OG.rawWeightBlock W := by
  letI := OG.isAlgClosed
  letI := OG.ambientBlockData.fintypeBlock
  letI := (OG.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI := (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).fintypeBlock
  have sourceInduction := inducedBlock_spec
    (Subgroup.normalizer (W.subgroup : Set G))
    (OG.inflatedNormalizerBlockData W.subgroup).catalogue
    OG.ambientBlockData.catalogue (ownNormalizerBlock OG W)
    (OG.blockInductionDefined W)
  have transported := @blockInducesTo_alongMulEquiv k G H
    _ OG.isAlgClosed _ _ _ _
    (Subgroup.normalizer (W.subgroup : Set G))
    (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H))
    _ Block _ Block
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
    (ownNormalizerBlock OH (W.mapGroupEquiv e)) (OG.rawWeightBlock W)
    (ownCentralCharacter_transport OG OH e dictionary W)
    (ambientCentralCharacter_transport OG OH e dictionary (OG.rawWeightBlock W))
    sourceInduction
  letI := OH.ambientBlockData.fintypeBlock
  have unique := eq_inducedBlock_of_blockInducesTo
    (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H))
    (OH.inflatedNormalizerBlockData (W.mapGroupEquiv e).subgroup).catalogue
    OH.ambientBlockData.catalogue (ownNormalizerBlock OH (W.mapGroupEquiv e))
    (OH.blockInductionDefined (W.mapGroupEquiv e)) transported
  simpa only [LocalBlockInductionOperations.rawWeightBlock,
    LocalBlockInductionOperations.induceToAmbient, ownNormalizerBlock] using unique.symm

section Action

variable [MulAction (MulAut G)ᵐᵒᵖ Block]

/-- The actual opposite automorphism map used to pull back the block action. -/
def oppositeAutPullback (e : G ≃* H) : (MulAut H)ᵐᵒᵖ →* (MulAut G)ᵐᵒᵖ where
  toFun a := MulOpposite.op (MulAut.congr e.symm a.unop)
  map_one' := by
    change MulOpposite.op (MulAut.congr e.symm 1) = 1
    exact congrArg MulOpposite.op (map_one (MulAut.congr e.symm))
  map_mul' a b := by
    change MulOpposite.op (MulAut.congr e.symm (b.unop * a.unop)) =
      MulOpposite.op (MulAut.congr e.symm a.unop) *
        MulOpposite.op (MulAut.congr e.symm b.unop)
    exact congrArg MulOpposite.op (map_mul (MulAut.congr e.symm) b.unop a.unop)

/-- The target block action is constructed from the original action and e. -/
@[instance_reducible]
def transportedBlockAction (e : G ≃* H) : MulAction (MulAut H)ᵐᵒᵖ Block :=
  MulAction.compHom Block (oppositeAutPullback e)

@[simp] theorem transportedBlockAction_smul (a : (MulAut H)ᵐᵒᵖ) (b : Block) :
    letI := transportedBlockAction (Block := Block) e
    a • b = MulOpposite.op (MulAut.congr e.symm a.unop) • b := rfl

/-- An actual inverse-coordinate identity for the automorphism maps. -/
theorem congr_symm_congr (alpha : MulAut H) :
    MulAut.congr e (MulAut.congr e.symm alpha) = alpha := by
  apply MulEquiv.ext
  intro x
  simp [MulAut.congr]

/-- The target operation laws are derived from the old source and the
primitive dictionary, with the transported block action fixed above. -/
def transportedSource
    (S : LocalBlockInductionSource (p := p) (k := k) (K := K)
      (G := G) (Block := Block))
    (dictionary : PrimitiveDictionary S.operations OH e) :
    letI := transportedBlockAction (Block := Block) e
    LocalBlockInductionSource (p := p) (k := k) (K := K)
      (G := H) (Block := Block) := by
  letI := transportedBlockAction (Block := Block) e
  exact {
    operations := OH
    automorphism_transport alpha V := by
      let W := V.mapGroupEquiv e.symm
      have hV : W.mapGroupEquiv e = V := mapGroupEquiv_mapGroupEquiv_symm V e
      have ht : (W.rightTwist (MulAut.congr e.symm alpha)).mapGroupEquiv e =
          V.rightTwist alpha := by
        rw [mapGroupEquiv_rightTwist, hV, congr_symm_congr e alpha]
      calc
        OH.rawWeightBlock (V.rightTwist alpha) =
            S.operations.rawWeightBlock (W.rightTwist (MulAut.congr e.symm alpha)) := by
          rw [← ht]
          exact rawWeightBlock_eq S.operations OH e dictionary _
        _ = MulOpposite.op (MulAut.congr e.symm alpha) • S.operations.rawWeightBlock W :=
          S.automorphism_transport _ W
        _ = MulOpposite.op alpha • OH.rawWeightBlock V := by
          change MulOpposite.op (MulAut.congr e.symm alpha) • S.operations.rawWeightBlock W =
            MulOpposite.op (MulAut.congr e.symm alpha) • OH.rawWeightBlock V
          rw [← rawWeightBlock_eq S.operations OH e dictionary W, hV]
    inner_blocks_fixed h b := by
      change MulOpposite.op (MulAut.congr e.symm (MulAut.conj h⁻¹)) • b = b
      have hconj : MulAut.congr e.symm (MulAut.conj h⁻¹) =
          MulAut.conj (e.symm h)⁻¹ := by
        apply MulEquiv.ext
        intro x
        simp [MulAut.congr, MulAut.conj_apply, map_mul, map_inv]
      rw [hconj]
      exact S.inner_blocks_fixed (e.symm h) b }

variable
    (S : LocalBlockInductionSource (p := p) (k := k) (K := K)
      (G := G) (Block := Block))
    (sourceDictionary : PrimitiveDictionary S.operations OH e)

/-- Both existing quotients retain the same computed block label. -/
theorem weightBlock_eq
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    letI := transportedBlockAction (Block := Block) e
    (transportedSource OH e S sourceDictionary).weightBlock
        (CharacterWeight.conjugacyClassGroupEquiv e w) = S.weightBlock w := by
  letI := transportedBlockAction (Block := Block) e
  refine Quotient.inductionOn w ?_
  intro x
  refine Quotient.inductionOn x ?_
  intro W
  exact rawWeightBlock_eq S.operations OH e sourceDictionary W

/-- The block fibre equivalence restricts the computed actual class map. -/
def fibreEquiv (b : Block) :
    letI := transportedBlockAction (Block := Block) e
    S.Fibre b ≃ (transportedSource OH e S sourceDictionary).Fibre b := by
  letI := transportedBlockAction (Block := Block) e
  exact {
    toFun w := ⟨CharacterWeight.conjugacyClassGroupEquiv e w.1,
      (weightBlock_eq OH e S sourceDictionary w.1).trans w.2⟩
    invFun v := ⟨(CharacterWeight.conjugacyClassGroupEquiv e).symm v.1, by
      have h := weightBlock_eq OH e S sourceDictionary
        ((CharacterWeight.conjugacyClassGroupEquiv e).symm v.1)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans v.2⟩
    left_inv w := by
      apply Subtype.ext
      exact (CharacterWeight.conjugacyClassGroupEquiv e).symm_apply_apply w.1
    right_inv v := by
      apply Subtype.ext
      exact (CharacterWeight.conjugacyClassGroupEquiv e).apply_symm_apply v.1 }

@[simp] theorem fibreEquiv_val (b : Block) (w : S.Fibre b) :
    (fibreEquiv OH e S sourceDictionary b w).1 =
      CharacterWeight.conjugacyClassGroupEquiv e w.1 := rfl

end Action

end ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
