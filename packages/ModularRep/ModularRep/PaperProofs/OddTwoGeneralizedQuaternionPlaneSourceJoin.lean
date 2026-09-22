import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
import Mathlib.GroupTheory.Sylow

/-!
# The actual generalized-quaternion plane in the principal x-1 fibre

This is the remaining single-basic case-(6) slice with gamma_FM = 0 and
a >= 3. The base is an actual Sylow 2-subgroup of the symplectic plane;
its standard E1 type is QuaternionGroup (2^(a-1)), of order 2^(a+1).
No generalized-quaternion matrix representation is reconstructed.

Carter--Fong (1964), Section I, case II, p. 143, gives this plane Sylow
type and the order of Sp_2(q). FYZ, p. 29, defines R^4_{alpha,gamma}
using Q_(2^(a+alpha+1)) on a symplectic space of dimension 2^(alpha+1).
At alpha = gamma = 0 this is precisely the plane above, followed by
multiplicity one and the actual source wreath construction. The field
parameter is a = v_2(q^2-1)-1, not the defining characteristic.

The narrow group-only E2 coverage statement below ranges over every actual
plane subgroup of this exact type, with the same wreath list and matrix
coordinates. Such a plane subgroup has Sylow order, so the source argument
is plane Sylow conjugacy followed by its repeated wreath conjugator.
The whole wreath subgroup is not asserted to be Sylow for arbitrary lists.

An (2B)(c), p. 169, the construction on p. 176 and (4F)(d), p. 189, bind
this model to Q_(1,0,0). An (2H)(a), p. 179, (4G), p. 191, and (6.1),
p. 195, supply radicality and one local defect-zero character for every
fixed admissible wreath list. The scalar centralizer is contained in the
subgroup, so the source centralizer character is trivial and its count
concerns all the local quotient characters used here.

The a = 2 three-character exception is separate. For a >= 3, this model
has plane order at least 16; the two additional Q8 classes at gamma_FM = 0
are handled separately by the existing quaternion class-pair module.
There is no assertion about positive gamma, products, named source-character
labels, or their diagonal action. K below composes subgroup conjugacy and
uses actual local uniqueness to derive the principal class and its own
normalizer block induction. No principal membership or character match is
an external field.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoGeneralizedQuaternionPlaneSourceJoin

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoQuaternionFactor
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.OddTwoSourceWreathAction
open ModularRep.PaperProofs.OddTwoWreathReflection
open ModularRep.PaperProofs.OddTwoAmbientRealisation
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.NavarroLocalReductionInflationBlockCompatibility

universe u

variable {n : ℕ} {F : Type u} [Field F] [Fintype F]

local instance pointsFintype (cs : List ℕ) : Fintype (SourceWreathPoints cs) :=
  Fintype.ofFinite _
local instance pointsDecidableEq (cs : List ℕ) : DecidableEq (SourceWreathPoints cs) :=
  Classical.decEq _
local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

/-- The actual source plane, followed by standard E1 Gram/reindex
coordinates. The empty list represents the source's trivial wreath `(0)`;
nonempty lists have positive entries and are stored in FYZ order. -/
structure GeneralizedQuaternionPlaneModel (n : ℕ) (F : Type u)
    [Field F] [Fintype F] where
  fieldOdd : Odd (Nat.card F)
  a : ℕ
  a_ge_three : 3 ≤ a
  twoPart : (Nat.card F ^ 2 - 1).factorization 2 = a + 1
  planeSylow : Sylow 2 (FormIsometryGroup (omega (F := F)))
  /-- Carter--Fong p. 143, under this exact field parameter. Mathlib's
  QuaternionGroup t has order 4t, hence the index is 2^(a-1). -/
  quaternionType : QuaternionGroup (2 ^ (a - 1)) ≃* planeSylow
  wreathList : List ℕ
  wreath_positive : ∀ c ∈ wreathList, 0 < c
  rank_eq : n = 2 ^ wreathList.sum
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

namespace GeneralizedQuaternionPlaneModel

variable (C : GeneralizedQuaternionPlaneModel n F)

def base : Subgroup (FormIsometryGroup (omega (F := F))) :=
  C.planeSylow.toSubgroup

def baseQuaternionEquiv : QuaternionGroup (2 ^ (C.a - 1)) ≃* C.base :=
  C.quaternionType

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

/-- Every model element uses the same actual source wreath matrix and
specified coordinate reindexing. The abstract quaternion type does not
replace this ambient subgroup formula. -/
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

end GeneralizedQuaternionPlaneModel

variable (C : GeneralizedQuaternionPlaneModel n F)

/-- Narrow group-only E2 coverage at this fixed wreath list. The source
proof uses the actual plane's Sylow conjugacy and repeats its conjugator
through the source wreath matrices. It contains no character or principal
claim and does not identify the two different order-eight plane classes. -/
structure GeneralizedQuaternionClassCoverage : Prop where
  covers : ∀ E : Subgroup (FormIsometryGroup (omega (F := F))),
    Nonempty (QuaternionGroup (2 ^ (C.a - 1)) ≃* E) →
      ∃ g : Sp n F,
        (C.subgroupWithBase E).comap (MulAut.conj g⁻¹).toMonoidHom = C.subgroup

/-- The actual FYZ single-basic formula for R^4_(1,0,0,c), up to genuine
ambient conjugacy. A case number or source name alone is insufficient.
No local character match, weight-class equality or principal conclusion
is stored here. -/
structure SingleGeneralizedQuaternionWreathRealisation (R : Subgroup (Sp n F)) where
  base : Subgroup (FormIsometryGroup (omega (F := F)))
  quaternionType : Nonempty (QuaternionGroup (2 ^ (C.a - 1)) ≃* base)
  conjugator : Sp n F
  subgroup_formula : R.comap (MulAut.conj conjugator⁻¹).toMonoidHom =
    C.subgroupWithBase base

/-- K: compose the actual source-coordinate conjugacy and the fixed-list
group-only classification to obtain the model's subgroup match. -/
theorem subgroupMatch_of_realisation (A : GeneralizedQuaternionClassCoverage C)
    (R : Subgroup (Sp n F)) (T : SingleGeneralizedQuaternionWreathRealisation C R) :
    ∃ g : Sp n F, R.comap (MulAut.conj g⁻¹).toMonoidHom = C.subgroup := by
  obtain ⟨g, hg⟩ := A.covers T.base T.quaternionType
  refine ⟨g * T.conjugator, ?_⟩
  have hcomp : (MulAut.conj (g * T.conjugator)⁻¹).toMonoidHom =
      (MulAut.conj T.conjugator⁻¹).toMonoidHom.comp
        (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.comap_comap, T.subgroup_formula]
  exact hg

variable {k K Block : Type u} [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Exact An (4F)(d), (4G), and (6.1) local inputs at this actual model.
Ordinary splitting is explicit. Since the source scalar centralizer lies
in R, theta = 1 and N(theta) = N(R), so the count is all the displayed
local defect-zero characters. The three-character a=2 case is excluded
by the model's exact field parameter. -/
structure AnGeneralizedQuaternionLocalSource : Prop where
  ordinarySplitting : IsAlgClosed K
  radical : IsRadicalSubgroup 2 C.subgroup
  local_exists : Nonempty (LocalDefectZeroCharacters (K := K) C.subgroup)
  local_unique : Subsingleton (LocalDefectZeroCharacters (K := K) C.subgroup)

namespace AnGeneralizedQuaternionLocalSource

variable (S : AnGeneralizedQuaternionLocalSource (K := K) C)

def selectedLocal : LocalDefectZeroCharacters (K := K) C.subgroup :=
  Classical.choice S.local_exists

def rawPair : CharacterWeight 2 K (Sp n F) where
  prime := Nat.prime_two
  subgroup := C.subgroup
  radical := S.radical
  localCharacter := (S.selectedLocal C).1
  defectZero := (S.selectedLocal C).2

variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (w : D.PrincipalWeight) (g : Sp n F)
variable (hQ : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
  (MulAut.conj g⁻¹)).subgroup = C.subgroup)

/-- Actual local uniqueness identifies the chosen model character with
the transported character of the selected principal pair. -/
def principalWeight : D.FengMallePrincipalWeight :=
  fengMalleWeightOfConjugateUnique D w (S.rawPair C) g hQ S.local_unique

theorem principalWeight_eq :
    S.principalWeight C D w g hQ = D.intrinsicWeightEquiv w :=
  fengMalleWeightOfConjugateUnique_eq D w (S.rawPair C) g hQ S.local_unique

include C S D w g hQ in
theorem rawPair_principalBlock :
    D.blockSource.operations.rawWeightBlock (S.rawPair C) = D.principalBlock :=
  conjugateUniquePair_principalBlock D w (S.rawPair C) g hQ S.local_unique

include C S D w g hQ in
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

include w g hQ in
/-- The shared compatible-root source law identifies the block of the
model's own actual inflated reduction. K combines it with the proved
operations endpoint; ambient induction is not a new source premise. -/
theorem rawPair_actualBlockInducesTo
    (support : OddTwoActualLocalBlockSupport.Source D.iota D.blockSource.operations)
    (iotaN : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer ((S.rawPair C).subgroup : Set (Sp n F))))
    (phiN : IBr iotaN)
    (hroots : OddTwoActualLocalBlockSupport.RootCompatibleAlong D.iota iotaN
      (Subgroup.normalizer ((S.rawPair C).subgroup : Set (Sp n F))).subtype)
    (hReduction : NormalizerInflatedReduction
      (S.rawPair C).subgroup (S.rawPair C).localCharacter iotaN phiN) :
    let V := S.rawPair C
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData V.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (normalizerBrauerBlock O V.subgroup iotaN phiN) D.principalBlock := by
  exact OddTwoActualLocalBlockSupport.blockInducesTo_actualNormalizerBlock support
    (S.rawPair C) iotaN phiN hroots hReduction D.principalBlock
    (S.rawPair_blockInducesTo C D w g hQ)

/-- The actual FYZ single-basic realization and group-only coverage supply
the match. The principal fibre equation is then proved from local
uniqueness, without assuming a candidate principal class or character match.
-/
theorem exists_principalPair_of_realisation
    (A : GeneralizedQuaternionClassCoverage C)
    (T : SingleGeneralizedQuaternionWreathRealisation C
      (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup) :
    ∃ (g : Sp n F)
      (h : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹)).subgroup = C.subgroup),
      S.principalWeight C D w g h = D.intrinsicWeightEquiv w := by
  obtain ⟨g, hg⟩ := subgroupMatch_of_realisation C A _ T
  have h : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj g⁻¹)).subgroup = C.subgroup := hg
  exact ⟨g, h, S.principalWeight_eq C D w g h⟩

end AnGeneralizedQuaternionLocalSource

end ModularRep.PaperProofs.OddTwoGeneralizedQuaternionPlaneSourceJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
