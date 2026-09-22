import ModularRep.PaperProofs.OddTwoGeneralizedQuaternionPlaneSourceJoin
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The positive-gamma case-(6) tensor construction

The abstract plus extraspecial group is the specified central quotient of
gamma copies of D8. Its standard faithful orthogonal module and the plane
Sylow type are precise E1 inputs. The tensor representation is constrained
by its actual matrix formula and its diagonal central kernel. Its range,
source wreath image and final matrix coordinates are literal.

FYZ p.29 and Proposition 3.48(6), An p.176, (2H)(a), (4F)(d), (4G), and
(6.1) license the fixed-parameter source construction, class coverage and
local Fin1 enumeration. Both a=2 and a>=3 occur, but gamma is positive;
the gamma=0 three-character exception and the two case-(3) Q8 classes stay
in their existing checked modules. No general case-(3) gamma is invented.

K composes the source conjugators and consumes the actual selected local
enumeration and compatible block-support joins. Neither a character match
nor candidate principal membership is a source premise. Product radicals,
named actions, the complete principal family and iBAW are not asserted.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoQuaternionTensorSourceJoin

open scoped BigOperators Kronecker
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoQuaternionFactor
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.OddTwoSourceWreathAction
open ModularRep.PaperProofs.OddTwoWreathReflection
open ModularRep.PaperProofs.OddTwoAmbientRealisation
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-- The literal central tuples with even total exponent. The normal closure
gives a canonical quotient without rebuilding the central-product theory. -/
def evenCentralKernel (gamma : ℕ) : Subgroup (Fin gamma → DihedralGroup 4) :=
  Subgroup.normalClosure { x | ∃ epsilon : Fin gamma → Fin 2,
    (∑ i, (epsilon i).val) % 2 = 0 ∧
      ∀ i, x i = (DihedralGroup.r (2 : ZMod 4)) ^ (epsilon i).val }

instance (gamma : ℕ) : (evenCentralKernel gamma).Normal := by
  unfold evenCentralKernel
  infer_instance

/-- The standard central product of gamma D8 factors. -/
abbrev ExtraspecialPlus (gamma : ℕ) :=
  (Fin gamma → DihedralGroup 4) ⧸ evenCentralKernel gamma

/-- The common central involution, represented in the first factor. -/
def extraspecialCentral (gamma : ℕ) (hgamma : 0 < gamma) : ExtraspecialPlus gamma :=
  QuotientGroup.mk' (evenCentralKernel gamma)
    (Function.update 1 (⟨0, hgamma⟩ : Fin gamma) (DihedralGroup.r (2 : ZMod 4)))

universe u
variable {F : Type u} [Field F] [Fintype F]

def tensorGram (gamma : ℕ) :
    Matrix (Fin 2 × Fin (2 ^ gamma)) (Fin 2 × Fin (2 ^ gamma)) F :=
  omega (F := F) ⊗ₖ (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F)

/-- Exact standard E1 representation data on the fixed central-product
domain. The tensor map's matrix and kernel pin the actual embedding. -/
structure PositiveGammaBase (a gamma : ℕ) (F : Type u) [Field F] [Fintype F] where
  fieldOdd : Odd (Nat.card F)
  a_ge_two : 2 ≤ a
  gamma_positive : 0 < gamma
  twoPart : (Nat.card F ^ 2 - 1).factorization 2 = a + 1
  planeSylow : Sylow 2 (FormIsometryGroup (omega (F := F)))
  quaternionType : QuaternionGroup (2 ^ (a - 1)) ≃* planeSylow
  planeCentral : planeSylow
  planeCentral_matrix : isometryMatrix (omega (F := F)) planeCentral.1 = -1
  orthogonalRepresentation : ExtraspecialPlus gamma →*
    FormIsometryGroup (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F)
  orthogonal_faithful : Function.Injective orthogonalRepresentation
  orthogonal_central : isometryMatrix
      (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F)
      (orthogonalRepresentation (extraspecialCentral gamma gamma_positive)) = -1
  tensorRepresentation : (planeSylow × ExtraspecialPlus gamma) →*
    FormIsometryGroup (tensorGram (F := F) gamma)
  tensor_matrix : ∀ x,
    isometryMatrix (tensorGram (F := F) gamma) (tensorRepresentation x) =
      isometryMatrix (omega (F := F)) x.1.1 ⊗ₖ
        isometryMatrix (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F)
          (orthogonalRepresentation x.2)
  tensor_kernel : tensorRepresentation.ker =
    Subgroup.zpowers (planeCentral, extraspecialCentral gamma gamma_positive)

namespace PositiveGammaBase

variable {a gamma : ℕ} (B : PositiveGammaBase a gamma F)

def subgroup : Subgroup (FormIsometryGroup (tensorGram (F := F) gamma)) :=
  B.tensorRepresentation.range

/-- The same existing left and right tensor constructors give the supplied
source tensor matrix; it is not an unconstrained isomorphism type. -/
theorem tensor_matrix_eq_existing_factors (x : B.planeSylow × ExtraspecialPlus gamma) :
    isometryMatrix (tensorGram (F := F) gamma) (B.tensorRepresentation x) =
      isometryMatrix (tensorGram (F := F) gamma)
        (leftTensorIsometryHom (omega (F := F))
          (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F) x.1.1 *
        rightTensorIsometryHom (omega (F := F))
          (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F)
          (B.orthogonalRepresentation x.2)) := by
  rw [B.tensor_matrix]
  change _ =
    (isometryMatrix (omega (F := F)) x.1.1 ⊗ₖ
      (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F)) *
    ((1 : Matrix (Fin 2) (Fin 2) F) ⊗ₖ
      isometryMatrix (1 : Matrix (Fin (2 ^ gamma)) (Fin (2 ^ gamma)) F)
        (B.orthogonalRepresentation x.2))
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

end PositiveGammaBase

local instance pointsFintype (cs : List ℕ) : Fintype (SourceWreathPoints cs) :=
  Fintype.ofFinite _
local instance pointsDecidableEq (cs : List ℕ) : DecidableEq (SourceWreathPoints cs) :=
  Classical.decEq _
local instance spFintype (n : ℕ) : Fintype (Sp n F) := Fintype.ofFinite _

/-- The actual positive-gamma basic tensor subgroup followed by its source
wreath and exact symplectic coordinates. -/
structure TensorWreathModel (n : ℕ) (F : Type u) [Field F] [Fintype F] where
  a : ℕ
  gamma : ℕ
  base : PositiveGammaBase a gamma F
  wreathList : List ℕ
  wreath_positive : ∀ c ∈ wreathList, 0 < c
  rank_eq : n = 2 ^ (gamma + wreathList.sum)
  basisIndex : ((Fin 2 × Fin (2 ^ gamma)) × SourceWreathPoints wreathList) ≃
    (Fin n ⊕ Fin n)
  gram_equation : Matrix.reindex basisIndex basisIndex
      (repeatedGram (Omega := SourceWreathPoints wreathList) (tensorGram (F := F) gamma)) =
    Matrix.J (Fin n) F
  coordinates : FormIsometryGroup
      (repeatedGram (Omega := SourceWreathPoints wreathList) (tensorGram (F := F) gamma)) ≃*
    Sp n F
  coordinates_matrix : ∀ g,
    (coordinates g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.reindex basisIndex basisIndex
        (isometryMatrix
          (repeatedGram (Omega := SourceWreathPoints wreathList) (tensorGram (F := F) gamma)) g)

namespace TensorWreathModel

variable {n : ℕ} (C : TensorWreathModel n F)

def subgroupWithBase (B : PositiveGammaBase C.a C.gamma F) : Subgroup (Sp n F) :=
  ((PermutationWreathProduct.coefficientSubgroup
    (rho := sourceWreathAction C.wreathList) B.subgroup).map
      (wreathIsometryHom (tensorGram (F := F) C.gamma)
        (sourceWreathAction C.wreathList))).map C.coordinates.toMonoidHom

def subgroup : Subgroup (Sp n F) := C.subgroupWithBase C.base

def fengMalleWreathList : List ℕ := fyzToFengMalleWreathList C.wreathList

theorem fengMalleWreathList_eq_reverse :
    C.fengMalleWreathList = C.wreathList.reverse := rfl

end TensorWreathModel

variable {n : ℕ} (C : TensorWreathModel n F)

/-- The single class of actual source tensor constructions at fixed a,
positive gamma and wreath list. An p.176 and FM Section5.1; group-only E2. -/
structure PositiveGammaClassCoverage : Prop where
  covers : ∀ B : PositiveGammaBase C.a C.gamma F,
    ∃ g : Sp n F,
      (C.subgroupWithBase B).comap (MulAut.conj g⁻¹).toMonoidHom = C.subgroup

/-- The selected FYZ subgroup has the actual tensor/wreath formula, up to
genuine ambient conjugacy. No character or principal conclusion is stored. -/
structure SingleTensorWreathRealisation (R : Subgroup (Sp n F)) where
  base : PositiveGammaBase C.a C.gamma F
  conjugator : Sp n F
  subgroup_formula : R.comap (MulAut.conj conjugator⁻¹).toMonoidHom =
    C.subgroupWithBase base

theorem subgroupMatch_of_realisation (A : PositiveGammaClassCoverage C)
    (R : Subgroup (Sp n F)) (T : SingleTensorWreathRealisation C R) :
    ∃ g : Sp n F, R.comap (MulAut.conj g⁻¹).toMonoidHom = C.subgroup := by
  obtain ⟨g, hg⟩ := A.covers T.base
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

/-- Exact fixed-basic local-character classification. An (4G)/(6.1);
positive gamma excludes the exceptional three-character case at a=2. -/
structure AnPositiveGammaLocalCharacters where
  ordinarySplitting : IsAlgClosed K
  enumeration : Fin 1 ≃ LocalDefectZeroCharacters (K := K) C.subgroup

variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block)) (w : D.PrincipalWeight)

/-- K selects the source enumeration index and proves its actual principal
FM fibre equation, consuming the existing own-character join. -/
theorem exists_principalPair_of_realisation
    (A : PositiveGammaClassCoverage C)
    (S : AnPositiveGammaLocalCharacters (K := K) C)
    (T : SingleTensorWreathRealisation C
      (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup) :
    ∃ (g : Sp n F)
      (h : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹)).subgroup = C.subgroup),
      principalWeight D w C.subgroup g h S.enumeration = D.intrinsicWeightEquiv w := by
  obtain ⟨g, hg⟩ := subgroupMatch_of_realisation C A _ T
  exact ⟨g, hg, principalWeight_eq D w C.subgroup g hg S.enumeration⟩

/-- The actual block of that same enumerated character's compatible
inflated reduction induces to the principal block. -/
theorem selectedPair_actualBlockInducesTo
    (S : AnPositiveGammaLocalCharacters (K := K) C) (g : Sp n F)
    (h : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj g⁻¹)).subgroup = C.subgroup)
    (support : OddTwoActualLocalBlockSupport.Source D.iota D.blockSource.operations)
    (iotaN : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer (C.subgroup : Set (Sp n F))))
    (phiN : IBr iotaN)
    (hroots : OddTwoActualLocalBlockSupport.RootCompatibleAlong D.iota iotaN
      (Subgroup.normalizer (C.subgroup : Set (Sp n F))).subtype)
    (hReduction : NormalizerInflatedReduction C.subgroup
      (selectedEnumeratedPair D w C.subgroup g h S.enumeration).localCharacter iotaN phiN) :
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData C.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo (Subgroup.normalizer (C.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (normalizerBrauerBlock O C.subgroup iotaN phiN) D.principalBlock := by
  exact OddTwoActualLocalBlockSupport.enumeratedPair_actualBlockInducesTo
    D support w C.subgroup g h S.enumeration iotaN phiN hroots hReduction

end ModularRep.PaperProofs.OddTwoQuaternionTensorSourceJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
