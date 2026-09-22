import ModularRep.PaperProofs.OddTwoFYZCompleteProductSourceJoin
import ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin

/-!
# The complete actual principal FYZ-to-Feng--Malle carrier join

The source supplies a JOINT choice for each actual principal weight: a
complete FYZ decomposition with compatible normalized basic bases and
grouping, its scoped factor sources, the full block-monomial normalizer of
the COMPUTED surviving product, and the actual An/FM local character
construction. It does not assert these sources for an arbitrary prior
decomposition. Individual conjugacies can be absorbed into the chosen
global symplectic coordinates before the joint data are supplied.

No full surviving-product match, selected local-character equality,
candidate principal membership or weight map is a field. K excludes every
corrected occurrence, obtains the product subgroup match, computes the
inverse-enumeration heights of the same own local character, and proves
that the resulting principal FM class is the original intrinsic class.
The explicit induced-character value on actual normalizer lifts is kept.

FYZ 3.37/3.48, the valid restricted exclusions of 3.50, equation (3.35),
An's basic classification and (3B)/(6D), and FM 5.4 are substantial E1/E2
inputs. Their joint source has not been instantiated here. In particular,
the full normalizer theorem is used on the product genuinely conjugate to
the selected radical, not on every unrestricted multiplicity vector.
Named diagonal/field labels, their actions, the modular-triple orbit
witness, Jordan reduction and central descent remain separate joins.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoFYZPrincipalFullCarrierJoin

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer
open ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin
open ModularRep.PaperProofs.OddTwoFYZCompleteProductSourceJoin
open ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [CharP k 2] [IsAlgClosed k]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

local instance basicQuotientFintype (P : ProductShape n F) (i : Fin P.count) :
    Fintype (BasicQuotient P i) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (fieldOdd : Odd (Nat.card F)) (lemma23 : FYZLemma23IntrinsicCertificate D)

/-- Jointly normalized complete source data for the SAME selected weight.
The normalizer and all local character data are indexed by the product
computed from factor exclusion, not by a separately supplied subgroup. -/
structure SelectedFullProductData (w : D.PrincipalWeight) where
  factors : FullFactorData (selectedCharacterWeight D.blockSource D.principalBlock w)
  factorSources : PrincipalFactorSources D w factors
  normalizer : AnProductNormalizerSource
    (factorSources.productShape fieldOdd lemma23)
    (factorSources.productGeometry fieldOdd lemma23)
  localCharacters : ∀ i,
    BasicModel.LocalEnumeration (K := K)
      ((factorSources.productShape fieldOdd lemma23).basic i)
  formula : CoreFormulaData
    (multiplicity := (factorSources.productShape fieldOdd lemma23).copies)
    (BasicQuotient (factorSources.productShape fieldOdd lemma23))
    (fun i => (localCharacters i).enumeration)
  characters : AnFMCoreCharacterSource
    (BasicQuotient (factorSources.productShape fieldOdd lemma23))
    (fun i => (localCharacters i).enumeration) formula

namespace SelectedFullProductData

variable {D fieldOdd lemma23} {w : D.PrincipalWeight}
variable (A : SelectedFullProductData D fieldOdd lemma23 w)

abbrev shape : ProductShape n F := A.factorSources.productShape fieldOdd lemma23

abbrev geometry : A.shape.Geometry := A.factorSources.productGeometry fieldOdd lemma23

/-- The complete subgroup equality is derived by the existing corrected
factor exclusion and substitutions in the original independent product. -/
theorem subgroup_match :
    ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj A.factors.conjugator⁻¹)).subgroup = A.geometry.subgroup :=
  A.factorSources.subgroup_match fieldOdd lemma23

/-- The coloured heights are computed from the selected own character. -/
def heights : Assignments A.shape :=
  selectedHeights A.shape A.geometry A.normalizer A.localCharacters A.formula A.characters
    D w A.factors.conjugator A.subgroup_match

def pair : CharacterWeight 2 K (Sp n F) :=
  selectedPair A.shape A.geometry A.normalizer A.localCharacters A.formula A.characters
    D w A.factors.conjugator A.subgroup_match

theorem pair_eq_twist :
    A.pair = (selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj A.factors.conjugator⁻¹) :=
  selectedPair_eq_twist A.shape A.geometry A.normalizer A.localCharacters A.formula
    A.characters D w A.factors.conjugator A.subgroup_match

/-- The own selected character is the exact induced tensor/core function
on every actual block-monomial normalizer lift. -/
theorem pair_character_on_lift (z : NormalizerWreaths A.shape) :
    A.pair.localCharacter
        (QuotientGroup.mk' (A.geometry.subgroup.subgroupOf
          (Subgroup.normalizer (A.geometry.subgroup : Set (Sp n F))))
            (A.normalizer.normalizerLift z)) =
      A.formula.characterFunction A.heights (quotientWreathMap A.shape z) :=
  selectedPair_character_on_lift A.shape A.geometry A.normalizer A.localCharacters
    A.formula A.characters D w A.factors.conjugator A.subgroup_match z

/-- Candidate principal membership is derived from equality of the actual
selected pair's class, not included in the source choice. -/
def principalWeight : D.FengMallePrincipalWeight :=
  OddTwoPrincipalProductCharacterJoin.principalWeight A.shape A.geometry A.normalizer
    A.localCharacters A.formula A.characters D w A.factors.conjugator A.subgroup_match

theorem principalWeight_eq : A.principalWeight = D.intrinsicWeightEquiv w :=
  OddTwoPrincipalProductCharacterJoin.principalWeight_eq A.shape A.geometry A.normalizer
    A.localCharacters A.formula A.characters D w A.factors.conjugator A.subgroup_match

end SelectedFullProductData

/-- The precise external complete source provider. Its quantifier is a
JOINT choice of suitably normalized data for each actual weight. It does
not promise basic normalization or separation for an arbitrary T. Every
character field remains the independent standard LOCAL construction. -/
structure JointSource : Prop where
  selected : ∀ w : D.PrincipalWeight,
    Nonempty (SelectedFullProductData D fieldOdd lemma23 w)

namespace JointSource

variable {D fieldOdd lemma23} (S : JointSource D fieldOdd lemma23)

def data (w : D.PrincipalWeight) : SelectedFullProductData D fieldOdd lemma23 w :=
  Classical.choice (S.selected w)

/-- The full carrier function follows the complete actual product and its
own-character construction for each selected principal weight. -/
def carrierMap (w : D.PrincipalWeight) : D.FengMallePrincipalWeight :=
  (S.data w).principalWeight

theorem carrierMap_apply (w : D.PrincipalWeight) :
    S.carrierMap w = D.intrinsicWeightEquiv w :=
  (S.data w).principalWeight_eq

theorem carrierMap_eq_intrinsic :
    S.carrierMap = (D.intrinsicWeightEquiv : D.PrincipalWeight → D.FengMallePrincipalWeight) :=
  funext S.carrierMap_apply

/-- Bijectivity is a K consequence of the proved equality of actual
classes. The forward map remains the computed full product construction. -/
def carrierEquiv : D.PrincipalWeight ≃ D.FengMallePrincipalWeight where
  toFun := S.carrierMap
  invFun := D.intrinsicWeightEquiv.symm
  left_inv w := by
    rw [S.carrierMap_apply]
    exact D.intrinsicWeightEquiv.symm_apply_apply w
  right_inv w := by
    rw [S.carrierMap_apply]
    exact D.intrinsicWeightEquiv.apply_symm_apply w

theorem carrierEquiv_eq_intrinsic : S.carrierEquiv = D.intrinsicWeightEquiv := by
  apply Equiv.ext
  exact S.carrierMap_apply

end JointSource

end ModularRep.PaperProofs.OddTwoFYZPrincipalFullCarrierJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
