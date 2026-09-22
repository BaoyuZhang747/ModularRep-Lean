import ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
import ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness

/-!
# An actual quaternion-wreath pair in the intrinsic principal fibre

This window uses the existing quaternion matrices and the existing source
wreath action. The only coordinate input is a standard E1 change of basis,
with its actual matrix formula and Gram equation. It is not a free abstract
identification of groups. No coordinate-theory library is rebuilt here.

The An (4F)(b), (4G), and (6.1) local input is restricted to the resulting
actual basic subgroup, with a >= 3. It supplies radicality and existence and
uniqueness of the actual defect-zero local character. A source application
must supply genuine conjugacy of the selected FYZ subgroup with this model.
No alpha class is assigned to an arbitrary quaternion embedding, and no
claim that one model covers both classes or arbitrary products is made.

K constructs the raw pair from these source facts and consumes the preceding
principal bridge to derive its actual FM fibre membership and block
induction. Neither conclusion is among the external source fields.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoQuaternionBasicSourceJoin

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoQuaternionFactor
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.OddTwoSourceWreathAction
open ModularRep.PaperProofs.OddTwoWreathReflection
open ModularRep.PaperProofs.OddTwoAmbientRealisation
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F : Type u} [Field F] [Fintype F]

local instance pointsFintype (cs : List ℕ) : Fintype (SourceWreathPoints cs) :=
  Fintype.ofFinite _
local instance pointsDecidableEq (cs : List ℕ) : DecidableEq (SourceWreathPoints cs) :=
  Classical.decEq _
local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

/-- Source parameters and routine E1 coordinates. The source a is the
two-adic parameter, not the field characteristic. The source wreath list
is stored in FYZ order; An/FM use its reversal. In this multiplicity-one
case a permutation of coordinates suffices. Since omega is the negative of
mathlib's two-dimensional J convention, the Gram equation fixes the sign.
-/
structure QuaternionBasicModel (n : ℕ) (F : Type u) [Field F] [Fintype F] where
  fieldOdd : Odd (Nat.card F)
  a : ℕ
  a_ge_three : 3 ≤ a
  twoPart : (Nat.card F ^ 2 - 1).factorization 2 = a + 1
  wreathList : List ℕ
  wreath_positive : ∀ c ∈ wreathList, 0 < c
  rank_eq : n = 2 ^ wreathList.sum
  x : F
  y : F
  quaternion_relation : x ^ 2 + y ^ 2 = -1
  basisIndex : (Fin 2 × SourceWreathPoints wreathList) ≃ (Fin n ⊕ Fin n)
  gram_equation : Matrix.reindex basisIndex basisIndex
      (repeatedGram (Omega := SourceWreathPoints wreathList) (omega (F := F))) =
    Matrix.J (Fin n) F
  coordinates : FormIsometryGroup
      (repeatedGram (Omega := SourceWreathPoints wreathList) (omega (F := F))) ≃*
    Sp n F
  coordinates_matrix : ∀ g,
    (coordinates g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.reindex basisIndex basisIndex
        (isometryMatrix
          (repeatedGram (Omega := SourceWreathPoints wreathList) (omega (F := F))) g)

namespace QuaternionBasicModel

variable (C : QuaternionBasicModel n F)

def base : Subgroup (FormIsometryGroup (omega (F := F))) :=
  (quaternionEmbedding C.x C.y C.quaternion_relation).range

/-- The base is the actual faithful quaternion matrix image. This does not
choose either of the two source alpha names. -/
def baseQuaternionEquiv : QuaternionGroup 2 ≃* C.base :=
  quaternionRangeEquiv C.x C.y C.quaternion_relation
    (two_ne_zero_of_odd_card C.fieldOdd)

def wreathSubgroupWithBase (E : Subgroup (FormIsometryGroup (omega (F := F)))) :
    Subgroup (FormIsometryGroup
    (repeatedGram (Omega := SourceWreathPoints C.wreathList) (omega (F := F)))) :=
  (PermutationWreathProduct.coefficientSubgroup
    (rho := sourceWreathAction C.wreathList) E).map
      (wreathIsometryHom (omega (F := F)) (sourceWreathAction C.wreathList))

def wreathSubgroup := C.wreathSubgroupWithBase C.base

def subgroupWithBase (E : Subgroup (FormIsometryGroup (omega (F := F)))) :
    Subgroup (Sp n F) :=
  (C.wreathSubgroupWithBase E).map C.coordinates.toMonoidHom

def subgroup : Subgroup (Sp n F) :=
  C.subgroupWithBase C.base

def fengMalleWreathList : List ℕ := fyzToFengMalleWreathList C.wreathList

theorem fengMalleWreathList_eq_reverse :
    C.fengMalleWreathList = C.wreathList.reverse := rfl

/-- The matrix of every actual model element is bound to the same source
wreath matrix and coordinate change. This is stronger than naming an
abstractly isomorphic subgroup. -/
theorem subgroup_element_matrix
    (z : PermutationWreathProduct (FormIsometryGroup (omega (F := F)))
      (sourceWreathAction C.wreathList))
    (hz : z ∈ PermutationWreathProduct.coefficientSubgroup
      (rho := sourceWreathAction C.wreathList) C.base) :
    let g := C.coordinates
      (wreathIsometryHom (omega (F := F)) (sourceWreathAction C.wreathList) z)
    g ∈ C.subgroup ∧
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        Matrix.reindex C.basisIndex C.basisIndex
          (wreathMatrix (omega (F := F)) (sourceWreathAction C.wreathList) z) := by
  constructor
  · exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩
  · exact C.coordinates_matrix _

end QuaternionBasicModel

variable {k K Block : Type u} [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (C : QuaternionBasicModel n F)

/-- Exact local E2 input for this actual basic subgroup: An (4F)(b), p. 189,
(4G), p. 191, and (6.1), p. 195, as used in FM Section 5.1. Ordinary splitting
is retained explicitly. Here C_G(R)=Z(G)<=R and the source centralizer
character is trivial; hence N(theta)=N(R) and all N(R)/R characters cover
theta. An's count therefore concerns all the local defect-zero characters
below. The a=2 three-character exception is outside C's range.
This packet contains no principal membership, character comparison,
weight equivalence, or block-induction assertion. -/
structure AnQuaternionBasicLocalSource : Prop where
  ordinarySplitting : IsAlgClosed K
  radical : IsRadicalSubgroup 2 C.subgroup
  local_exists : Nonempty (LocalDefectZeroCharacters (K := K) C.subgroup)
  local_unique : Subsingleton (LocalDefectZeroCharacters (K := K) C.subgroup)

namespace AnQuaternionBasicLocalSource

variable (S : AnQuaternionBasicLocalSource (K := K) C)

def selectedLocal : LocalDefectZeroCharacters (K := K) C.subgroup :=
  Classical.choice S.local_exists

def rawPair : CharacterWeight 2 K (Sp n F) where
  prime := Nat.prime_two
  subgroup := C.subgroup
  radical := S.radical
  localCharacter := (S.selectedLocal C).1
  defectZero := (S.selectedLocal C).2

variable (w : D.PrincipalWeight) (g : Sp n F)
variable (hQ : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
  (MulAut.conj g⁻¹)).subgroup = C.subgroup)

/-- The actual model pair enters the same intrinsic FM fibre by the proved
principal bridge. The genuine subgroup conjugacy is the remaining FYZ/An
classification input for this selected single-basic slice. -/
def principalWeight : D.FengMallePrincipalWeight :=
  fengMalleWeightOfConjugateUnique D w (S.rawPair C) g hQ S.local_unique

theorem principalWeight_eq :
    S.principalWeight D C w g hQ = D.intrinsicWeightEquiv w :=
  fengMalleWeightOfConjugateUnique_eq D w (S.rawPair C) g hQ S.local_unique

include D C S w g hQ in
theorem rawPair_principalBlock :
    D.blockSource.operations.rawWeightBlock (S.rawPair C) = D.principalBlock :=
  conjugateUniquePair_principalBlock D w (S.rawPair C) g hQ S.local_unique

include D C S w g hQ in
theorem rawPair_blockInducesTo :
    let V := S.rawPair C
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData V.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer V.subgroup
        (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      D.principalBlock :=
  conjugateUniquePair_blockInducesTo D w (S.rawPair C) g hQ S.local_unique

end AnQuaternionBasicLocalSource

end ModularRep.PaperProofs.OddTwoQuaternionBasicSourceJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
