import ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness

/-!
# Selecting the actual principal pair from a local character enumeration

An exhaustive enumeration of the ordinary defect-zero characters of the
actual normalizer quotient determines an index for the transported selected
local character. That index is constructed by the inverse enumeration.
The associated raw pair is then proved equal to the conjugated selected
weight, and hence has the same intrinsic principal class and induced block.

The enumeration is the narrow E2 local-character classification input. It
can have index type `Fin 3`, so this argument does not replace the a = 2
three-character exception by a uniqueness assumption. The source subgroup
conjugacy and interpretation of the ordinary splitting field remain E1/E2
obligations. No enumeration is constructed from a numerical character count.

All candidates use their own enumerated ordinary character. No candidate's
principal membership, character comparison, weight-class equality, block
induction or iBAW conclusion is a premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u v

section LocalEnumeration

variable {K G : Type u} [Field K] [CharZero K] [Group G] [Finite G]
variable {Index : Type v} {R : Subgroup G}

/-- A candidate raw pair uses the actual enumerated local character. -/
def enumeratedRawPair (R : Subgroup G) (radical : IsRadicalSubgroup 2 R)
    (enumeration : Index ≃ LocalDefectZeroCharacters (K := K) R)
    (i : Index) : CharacterWeight 2 K G where
  prime := Nat.prime_two
  subgroup := R
  radical := radical
  localCharacter := (enumeration i).1
  defectZero := (enumeration i).2

/-- The candidate subgroup's radicality follows from the genuine subgroup
match with an existing raw weight; no additional radicality source is needed. -/
theorem radical_of_rightTwist_subgroup_eq
    (W : CharacterWeight 2 K G) (alpha : MulAut G)
    (hR : (W.rightTwist alpha).subgroup = R) : IsRadicalSubgroup 2 R := by
  rw [← hR]
  exact (W.rightTwist alpha).radical

/-- The transported selected character, on the exact source subgroup R. -/
def transportedLocal (W : CharacterWeight 2 K G) (alpha : MulAut G)
    (hR : (W.rightTwist alpha).subgroup = R) :
    LocalDefectZeroCharacters (K := K) R :=
  ⟨castLocalCharacter hR (W.rightTwist alpha).localCharacter,
    castLocalCharacter_defectZero hR (W.rightTwist alpha).defectZero⟩

/-- The matching index is computed by the inverse of the actual local
enumeration, rather than selected by an external character comparison. -/
def matchingIndex (W : CharacterWeight 2 K G) (alpha : MulAut G)
    (hR : (W.rightTwist alpha).subgroup = R)
    (enumeration : Index ≃ LocalDefectZeroCharacters (K := K) R) : Index :=
  enumeration.symm (transportedLocal W alpha hR)

theorem enumeration_matchingIndex
    (W : CharacterWeight 2 K G) (alpha : MulAut G)
    (hR : (W.rightTwist alpha).subgroup = R)
    (enumeration : Index ≃ LocalDefectZeroCharacters (K := K) R) :
    enumeration (matchingIndex W alpha hR enumeration) =
      transportedLocal W alpha hR :=
  enumeration.apply_symm_apply _

/-- The chosen candidate agrees with the complete actual twisted raw pair.
The only comparison premise is the genuine subgroup equality. -/
theorem rightTwist_eq_enumeratedRawPair
    (W : CharacterWeight 2 K G) (alpha : MulAut G)
    (hR : (W.rightTwist alpha).subgroup = R)
    (enumeration : Index ≃ LocalDefectZeroCharacters (K := K) R) :
    W.rightTwist alpha =
      enumeratedRawPair R (radical_of_rightTwist_subgroup_eq W alpha hR)
        enumeration (matchingIndex W alpha hR enumeration) := by
  apply eq_of_isomorphic
  refine ⟨hR, ?_⟩
  exact (congrArg Subtype.val
    (enumeration_matchingIndex W alpha hR enumeration)).symm

end LocalEnumeration

section IntrinsicPrincipal

variable {n : ℕ} {F k K Block : Type u} {Index : Type v}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (w : D.PrincipalWeight) (R : Subgroup (Sp n F)) (g : Sp n F)
variable (hR : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
  (MulAut.conj g⁻¹)).subgroup = R)
variable (enumeration : Index ≃ LocalDefectZeroCharacters (K := K) R)

/-- The actual member of the source enumeration matching the conjugated
selected principal pair. Its character is the enumerated character at the
kernel-constructed matching index. -/
def selectedEnumeratedPair : CharacterWeight 2 K (Sp n F) :=
  enumeratedRawPair R
    (radical_of_rightTwist_subgroup_eq
      (selectedCharacterWeight D.blockSource D.principalBlock w)
      (MulAut.conj g⁻¹) hR)
    enumeration
    (matchingIndex (selectedCharacterWeight D.blockSource D.principalBlock w)
      (MulAut.conj g⁻¹) hR enumeration)

theorem selectedEnumeratedPair_eq_twist :
    selectedEnumeratedPair D w R g hR enumeration =
      (selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹) :=
  (rightTwist_eq_enumeratedRawPair
    (selectedCharacterWeight D.blockSource D.principalBlock w)
    (MulAut.conj g⁻¹) hR enumeration).symm

/-- The chosen local character is visibly the one from the source
enumeration; a block-compatible character is not chosen independently. -/
theorem selectedEnumeratedPair_localCharacter :
    (selectedEnumeratedPair D w R g hR enumeration).localCharacter =
      (enumeration
        (matchingIndex (selectedCharacterWeight D.blockSource D.principalBlock w)
          (MulAut.conj g⁻¹) hR enumeration)).1 := rfl

/-- The actual conjugacy class equality follows from the proved raw-pair
equality. -/
theorem selectedEnumeratedPair_class :
    (Quotient.mk'' (Quotient.mk'' (selectedEnumeratedPair D w R g hR enumeration)) :
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Sp n F)) = w.1 := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  have hpair : Isomorphic
      ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹)) (selectedEnumeratedPair D w R g hR enumeration) := by
    rw [selectedEnumeratedPair_eq_twist D w R g hR enumeration]
    exact isomorphic_refl _
  exact (weightClass_eq_of_conjugate_selectedPair g hpair).symm.trans
    (selectedCharacterWeight_spec D.blockSource D.principalBlock w)

/-- Principal membership is derived for the selected enumerated raw pair. -/
theorem selectedEnumeratedPair_principalBlock :
    D.blockSource.operations.rawWeightBlock
      (selectedEnumeratedPair D w R g hR enumeration) = D.principalBlock := by
  have h := congrArg D.blockSource.weightBlock
    (selectedEnumeratedPair_class D w R g hR enumeration)
  exact h.trans w.2

/-- The selected enumerated pair belongs to the same intrinsic FM fibre. -/
def principalWeight : D.FengMallePrincipalWeight :=
  ⟨Quotient.mk'' (Quotient.mk'' (selectedEnumeratedPair D w R g hR enumeration)),
    selectedEnumeratedPair_principalBlock D w R g hR enumeration⟩

theorem principalWeight_eq :
    principalWeight D w R g hR enumeration = D.intrinsicWeightEquiv w := by
  apply Subtype.ext
  exact selectedEnumeratedPair_class D w R g hR enumeration

/-- Actual block induction for this pair's own enumerated character and
its own normalizer, using only the existing local block operations. -/
theorem selectedEnumeratedPair_blockInducesTo :
    let V := selectedEnumeratedPair D w R g hR enumeration
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData V.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer V.subgroup
        (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      D.principalBlock := by
  let V := selectedEnumeratedPair D w R g hR enumeration
  let O := D.blockSource.operations
  let localData := O.inflatedNormalizerBlockData V.subgroup
  letI := O.ambientBlockData.fintypeBlock
  letI := localData.fintypeBlock
  have hblock : O.induceToAmbient V = D.principalBlock :=
    selectedEnumeratedPair_principalBlock D w R g hR enumeration
  change ModularRep.BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer V.subgroup
      (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
    D.principalBlock
  rw [← hblock]
  exact ModularRep.inducedBlock_spec
    (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer V.subgroup
      (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
    (O.blockInductionDefined V)

end IntrinsicPrincipal

end ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
