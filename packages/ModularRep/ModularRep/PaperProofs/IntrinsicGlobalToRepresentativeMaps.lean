import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions
import ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

/-!
# Representative local maps from an intrinsic global correspondence

For an actual radical subgroup Q, define the Brauer subset by the radical
class of its image under the global correspondence. The existing intrinsic
weight-fibre theorem then constructs the map to dz(N_G(Q)/Q). Its weight
class is the original global image, so block compatibility follows from the
same global block equation and actual local induction operations.

This is the representative-map part of Spath Definition 4.1(i)--(ii).
It does not supply the extension and intermediate-block assertions of (iii)
or the Q=1 normalizations in (iv), and makes no final iBAW claim.
-/

noncomputable section

namespace ModularRep.PaperProofs.IntrinsicGlobalToRepresentativeMaps

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete

universe u

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharZero K] [Group G] [Fintype G]
variable [CharP k p] [IsAlgClosed k]
variable (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
variable (omega : ModularRep.IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))

/-- The actual Brauer subset attached to a radical representative by the
global correspondence. No additional partition or local map is chosen. -/
abbrev BrauerAtRadical (Q : RadicalSubgroup (p := p) (G := G)) :=
  {psi : ModularRep.IBr iota // radicalClass (omega psi) =
    (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G))}

def brauerEquivWeightRadicalFibre (Q : RadicalSubgroup (p := p) (G := G)) :
    BrauerAtRadical iota omega Q ≃ WeightRadicalFibre (K := K) Q where
  toFun psi := ⟨omega psi.1, psi.2⟩
  invFun w := ⟨omega.symm w.1, by rw [omega.apply_symm_apply]; exact w.2⟩
  left_inv psi := Subtype.ext (omega.symm_apply_apply psi.1)
  right_inv w := Subtype.ext (omega.apply_symm_apply w.1)

/-- The literal representative-level bijection, with target the actual
defect-zero ordinary characters of the normalizer quotient. -/
def localMap (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G)) :
    BrauerAtRadical iota omega Q ≃ LocalDefectZeroCharacter (K := K) Q :=
  (brauerEquivWeightRadicalFibre iota omega Q).trans
    (localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).symm

theorem localMap_class (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G))
    (psi : BrauerAtRadical iota omega Q) :
    (Quotient.mk'' (Quotient.mk''
      (characterWeightAt hp Q (localMap iota omega hp Q psi))) :
        ConjugacyClass (p := p) (K := K) (G := G)) = omega psi.1 := by
  rw [← localDefectZeroEquivWeightRadicalFibre_apply_val]
  change ((localDefectZeroEquivWeightRadicalFibre (K := K) hp Q)
    ((localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).symm
      ⟨omega psi.1, psi.2⟩)).1 = omega psi.1
  exact congrArg Subtype.val
    ((localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).apply_symm_apply
      ⟨omega psi.1, psi.2⟩)

/-- Every Brauer character lies in a representative subset. -/
theorem exists_radical (psi : ModularRep.IBr iota) :
    ∃ Q : RadicalSubgroup (p := p) (G := G),
      radicalClass (omega psi) =
        (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)) := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (radicalClass (omega psi))
  exact ⟨Q, hQ.symm⟩

/-- Two representative subsets can intersect only for conjugate radicals. -/
theorem radical_classes_eq_of_common_member
    (Q R : RadicalSubgroup (p := p) (G := G)) (psi : ModularRep.IBr iota)
    (hQ : radicalClass (omega psi) =
      (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)))
    (hR : radicalClass (omega psi) =
      (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := G))) :
    (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)) =
      Quotient.mk'' R := hQ.symm.trans hR

/-- Transport of the actual local character through the normalizer quotient
map already used by the raw character-weight automorphism action. -/
def localCharacterTwist (hp : p.Prime)
    (Q : RadicalSubgroup (p := p) (G := G)) (a : (MulAut G)ᵐᵒᵖ)
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    LocalDefectZeroCharacter (K := K) (Q.rightTwist a.unop) :=
  ⟨((characterWeightAt hp Q theta).rightTwist a.unop).localCharacter,
    ((characterWeightAt hp Q theta).rightTwist a.unop).defectZero⟩

variable (equivariant : ∀ (a : (MulAut G)ᵐᵒᵖ) (psi : ModularRep.IBr iota),
  omega (a • psi) = a • omega psi)

include equivariant in
/-- The Brauer partition transforms by the actual automorphism of radicals. -/
def brauerTransport (a : (MulAut G)ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := p) (G := G))
    (psi : BrauerAtRadical iota omega Q) :
    BrauerAtRadical iota omega (Q.rightTwist a.unop) := by
  refine ⟨a • psi.1, ?_⟩
  rw [equivariant, radicalClass_equivariant, psi.2]
  rfl

include equivariant in
/-- The representative local bijections have the required automorphism
covariance with the actual quotient-character transport. No equivariance of
independently chosen raw weight representatives is assumed. -/
theorem localMap_covariance (hp : p.Prime)
    (a : (MulAut G)ᵐᵒᵖ) (Q : RadicalSubgroup (p := p) (G := G))
    (psi : BrauerAtRadical iota omega Q) :
    localMap iota omega hp (Q.rightTwist a.unop)
        (brauerTransport iota omega equivariant a Q psi) =
      localCharacterTwist hp Q a (localMap iota omega hp Q psi) := by
  apply (localDefectZeroEquivWeightRadicalFibre (K := K) hp
    (Q.rightTwist a.unop)).injective
  apply Subtype.ext
  rw [localDefectZeroEquivWeightRadicalFibre_apply_val,
    localDefectZeroEquivWeightRadicalFibre_apply_val, localMap_class]
  change omega (a • psi.1) = a •
    (Quotient.mk'' (Quotient.mk''
      (characterWeightAt hp Q (localMap iota omega hp Q psi))) :
        ConjugacyClass (p := p) (K := K) (G := G))
  rw [equivariant, localMap_class]

variable [MulAction (MulAut G)ᵐᵒᵖ Block]
variable (S : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G) (Block := Block))
variable (brauerBlock : ModularRep.IBr iota → Block)
variable (block_preserving : ∀ psi, S.weightBlock (omega psi) = brauerBlock psi)

include block_preserving in
/-- The representative character induces to the same block as the original
Brauer character. This uses the class equation, not a new matching premise. -/
theorem localMap_block (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G))
    (psi : BrauerAtRadical iota omega Q) :
    S.operations.rawWeightBlock
      (characterWeightAt hp Q (localMap iota omega hp Q psi)) =
        brauerBlock psi.1 := by
  have h := congrArg S.weightBlock (localMap_class iota omega hp Q psi)
  exact h.trans (block_preserving psi.1)

/-- The actual fixed-block part of the Brauer subset at a radical. -/
abbrev BrauerInBlockAtRadical
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block) :=
  {psi : BrauerAtRadical iota omega Q // brauerBlock psi.1 = b}

include block_preserving in
/-- Restriction of the derived local map to a fixed ambient block. The target
is the existing literal `RepresentativeDZ`, whose membership is the actual
induced-block equation. No extra bijection on that block is assumed. -/
def blockLocalMap (hp : p.Prime)
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block) :
    BrauerInBlockAtRadical iota omega brauerBlock Q b ≃ RepresentativeDZ hp S Q b := by
  refine (localMap iota omega hp Q).subtypeEquiv ?_
  intro psi
  change brauerBlock psi.1 = b ↔ S.operations.rawWeightBlock
    (characterWeightAt hp Q (localMap iota omega hp Q psi)) = b
  rw [localMap_block iota omega S brauerBlock block_preserving hp Q psi]

include block_preserving in
/-- Full block induction for the constructed normalizer-quotient character. -/
theorem localMap_blockInducesTo
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G))
    (psi : BrauerAtRadical iota omega Q) :
    let theta := localMap iota omega hp Q psi
    let O := S.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo (Subgroup.normalizer (Q.1 : Set G))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2))
      (brauerBlock psi.1) := by
  let W := characterWeightAt hp Q (localMap iota omega hp Q psi)
  let O := S.operations
  let localData := O.inflatedNormalizerBlockData Q.1
  letI := O.ambientBlockData.fintypeBlock
  letI := localData.fintypeBlock
  have hinduced : O.induceToAmbient W = brauerBlock psi.1 :=
    localMap_block iota omega S brauerBlock block_preserving hp Q psi
  change ModularRep.BlockInducesTo (Subgroup.normalizer (Q.1 : Set G))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer Q.1
      (O.localCharacterBlock Q.1 W.localCharacter W.defectZero))
    (brauerBlock psi.1)
  rw [← hinduced]
  exact ModularRep.inducedBlock_spec (Subgroup.normalizer (Q.1 : Set G))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer Q.1
      (O.localCharacterBlock Q.1 W.localCharacter W.defectZero))
    (O.blockInductionDefined W)

end ModularRep.PaperProofs.IntrinsicGlobalToRepresentativeMaps

namespace ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

open ModularRep.CharacterWeight

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
local instance representativeSpFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _

namespace LiteralGlobalMap

variable {P : LiteralFengMalleProblem n F} (omega : LiteralGlobalMap P)

/-- The concrete Sp application uses exactly the problem's literal Brauer
and sets of weights. The generic block function is fixed to `P.brauerBlock`
below; no alternative block labelling is accepted. -/
abbrev brauerAtRadical (Q : RadicalSubgroup (p := 2) (G := LiteralSp n F)) :=
  IntrinsicGlobalToRepresentativeMaps.BrauerAtRadical P.iota omega.equiv Q

def representativeLocalMap (Q : RadicalSubgroup (p := 2) (G := LiteralSp n F)) :
    omega.brauerAtRadical Q ≃ LocalDefectZeroCharacter (K := P.K) Q :=
  IntrinsicGlobalToRepresentativeMaps.localMap P.iota omega.equiv Nat.prime_two Q

def representativeBlockLocalMap
    (Q : RadicalSubgroup (p := 2) (G := LiteralSp n F))
    (b : LiteralPrimitiveBlock P.k (LiteralSp n F)) :
    IntrinsicGlobalToRepresentativeMaps.BrauerInBlockAtRadical
        P.iota omega.equiv P.brauerBlock Q b ≃
      RepresentativeDZ Nat.prime_two P.blockSource Q b :=
  IntrinsicGlobalToRepresentativeMaps.blockLocalMap P.iota omega.equiv
    P.blockSource P.brauerBlock omega.block_preserving Nat.prime_two Q b

theorem representativeLocalMap_block
    (Q : RadicalSubgroup (p := 2) (G := LiteralSp n F))
    (psi : omega.brauerAtRadical Q) :
    P.blockSource.operations.rawWeightBlock
      (characterWeightAt Nat.prime_two Q (omega.representativeLocalMap Q psi)) =
        P.brauerBlock psi.1 :=
  IntrinsicGlobalToRepresentativeMaps.localMap_block P.iota omega.equiv
    P.blockSource P.brauerBlock omega.block_preserving Nat.prime_two Q psi

/-- Literal block induction for the representative character derived from
this same global Sp correspondence. All local operations and block catalogues
are those of `P.blockSource`; no further matching or induction premise is
introduced. -/
theorem representativeLocalMap_blockInducesTo
    (Q : RadicalSubgroup (p := 2) (G := LiteralSp n F))
    (psi : omega.brauerAtRadical Q) :
    let theta := omega.representativeLocalMap Q psi
    let O := P.blockSource.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo (Subgroup.normalizer (Q.1 : Set (LiteralSp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2))
      (P.brauerBlock psi.1) :=
  IntrinsicGlobalToRepresentativeMaps.localMap_blockInducesTo P.iota omega.equiv
    P.blockSource P.brauerBlock omega.block_preserving Nat.prime_two Q psi

theorem representativeLocalMap_covariance
    (a : (MulAut (LiteralSp n F))ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := LiteralSp n F))
    (psi : omega.brauerAtRadical Q) :
    omega.representativeLocalMap (Q.rightTwist a.unop)
        (IntrinsicGlobalToRepresentativeMaps.brauerTransport
          P.iota omega.equiv omega.equivariant a Q psi) =
      IntrinsicGlobalToRepresentativeMaps.localCharacterTwist Nat.prime_two Q a
        (omega.representativeLocalMap Q psi) :=
  IntrinsicGlobalToRepresentativeMaps.localMap_covariance P.iota omega.equiv
    omega.equivariant Nat.prime_two a Q psi

end LiteralGlobalMap

end ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
