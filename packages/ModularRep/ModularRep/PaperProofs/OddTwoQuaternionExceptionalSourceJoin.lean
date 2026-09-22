import ModularRep.PaperProofs.OddTwoQuaternionBasicSourceJoin
import ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin

/-!
# The actual case-(6) quaternion slice with three local characters

Here the source parameter is exactly a = 2 and gamma_FM = 0. FYZ p. 29
identifies this case-(6) base with the minus extraspecial quaternion plane
group, followed by multiplicity one and the same source wreath construction.
An (1G)(b) gives one plane subgroup class; repeating its symplectic
conjugator gives the group-only coverage input below. An (4G) and (6.1)
give three local defect-zero characters for every fixed admissible wreath
list, including nonempty lists.

The model uses the actual quaternion matrices, source wreath action, and
constrained matrix coordinates. The ordinary-character enumeration is an
exact E2 input at this subgroup. K chooses its index from the transported
selected character; no uniqueness or character-match premise is introduced.
The chosen pair's principal membership follows in the existing intrinsic
operations-defined fibre. Interpreting its local block operation as the
block of the actual ordinary inflation additionally uses the common-root
block-support source law; the enumeration is not that law.

No named source-character labels or diagonal-action permutation are asserted.
The general gamma > 0 tensor family and products remain separate windows.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoQuaternionExceptionalSourceJoin

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

/-- The separate a=2 model keeps the checked nonexceptional model's range
unchanged. The empty list means the source's trivial wreath `(0)`. -/
structure QuaternionExceptionalModel (n : ℕ) (F : Type u)
    [Field F] [Fintype F] where
  fieldOdd : Odd (Nat.card F)
  twoPart : (Nat.card F ^ 2 - 1).factorization 2 = 3
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

namespace QuaternionExceptionalModel

variable (C : QuaternionExceptionalModel n F)

def base : Subgroup (FormIsometryGroup (omega (F := F))) :=
  (quaternionEmbedding C.x C.y C.quaternion_relation).range

def baseQuaternionEquiv : QuaternionGroup 2 ≃* C.base :=
  quaternionRangeEquiv C.x C.y C.quaternion_relation
    (two_ne_zero_of_odd_card C.fieldOdd)

def wreathSubgroupWithBase (E : Subgroup (FormIsometryGroup (omega (F := F)))) :
    Subgroup (FormIsometryGroup
      (repeatedGram (Omega := SourceWreathPoints C.wreathList) (omega (F := F)))) :=
  (PermutationWreathProduct.coefficientSubgroup
    (rho := sourceWreathAction C.wreathList) E).map
      (wreathIsometryHom (omega (F := F)) (sourceWreathAction C.wreathList))

def subgroupWithBase (E : Subgroup (FormIsometryGroup (omega (F := F)))) :
    Subgroup (Sp n F) :=
  (C.wreathSubgroupWithBase E).map C.coordinates.toMonoidHom

def subgroup : Subgroup (Sp n F) := C.subgroupWithBase C.base

def fengMalleWreathList : List ℕ := fyzToFengMalleWreathList C.wreathList

theorem fengMalleWreathList_eq_reverse :
    C.fengMalleWreathList = C.wreathList.reverse := rfl

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

end QuaternionExceptionalModel

variable (C : QuaternionExceptionalModel n F)

/-- An's one plane class, repeated through the same actual wreath action
and coordinates. This is a group-only E2 statement, not a weight match. -/
structure AnExceptionalClassCoverage : Prop where
  covers : ∀ E : Subgroup (FormIsometryGroup (omega (F := F))),
    Nonempty (QuaternionGroup 2 ≃* E) →
      ∃ g : Sp n F,
        (C.subgroupWithBase E).comap (MulAut.conj g⁻¹).toMonoidHom = C.subgroup

/-- The actual FYZ single-basic formula, rather than a case-(6) tag. -/
structure SingleExceptionalWreathRealisation (R : Subgroup (Sp n F)) where
  base : Subgroup (FormIsometryGroup (omega (F := F)))
  quaternionType : Nonempty (QuaternionGroup 2 ≃* base)
  conjugator : Sp n F
  subgroup_formula : R.comap (MulAut.conj conjugator⁻¹).toMonoidHom =
    C.subgroupWithBase base

theorem subgroupMatch_of_realisation (A : AnExceptionalClassCoverage C)
    (R : Subgroup (Sp n F)) (T : SingleExceptionalWreathRealisation C R) :
    ∃ g : Sp n F, R.comap (MulAut.conj g⁻¹).toMonoidHom = C.subgroup := by
  obtain ⟨g, hg⟩ := A.covers T.base T.quaternionType
  refine ⟨g * T.conjugator, ?_⟩
  have hcomp : (MulAut.conj (g * T.conjugator)⁻¹).toMonoidHom =
      (MulAut.conj T.conjugator⁻¹).toMonoidHom.comp
        (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [hcomp, ← Subgroup.comap_comap, T.subgroup_formula]
  exact hg

variable {k K Block : Type u} [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- An (4G)/(6.1) on this fixed basic subgroup, over the same ordinary
splitting field. The index has no named-label or action interpretation.
In particular this is not a claim that all three pairs are principal. -/
structure AnExceptionalLocalCharacters where
  ordinarySplitting : IsAlgClosed K
  enumeration : Fin 3 ≃ LocalDefectZeroCharacters (K := K) C.subgroup

variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block)) (w : D.PrincipalWeight)

/-- The group-only source classification now selects a member of the
actual three-character enumeration and proves its principal FM class.
The matching index itself is the inverse enumeration of the conjugated
selected local character, inside the imported K construction. -/
theorem exists_principalPair_of_realisation
    (A : AnExceptionalClassCoverage C)
    (S : AnExceptionalLocalCharacters (K := K) C)
    (T : SingleExceptionalWreathRealisation C
      (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup) :
    ∃ (g : Sp n F)
      (h : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹)).subgroup = C.subgroup),
      OddTwoPrincipalLocalEnumerationJoin.principalWeight D w C.subgroup g h
        S.enumeration = D.intrinsicWeightEquiv w := by
  obtain ⟨g, hg⟩ := subgroupMatch_of_realisation C A _ T
  exact ⟨g, hg, OddTwoPrincipalLocalEnumerationJoin.principalWeight_eq
    D w C.subgroup g hg S.enumeration⟩

end ModularRep.PaperProofs.OddTwoQuaternionExceptionalSourceJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
