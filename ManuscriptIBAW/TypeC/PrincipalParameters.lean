import ManuscriptIBAW.TypeC.PrincipalProducts

/-!
# Reconstruction from the surviving product parameters

The subgroup classification used here supplies representatives of conjugacy
classes of surviving product subgroups. Its source clauses concern subgroups
only. The parameters are a representative index together with a staircase
height for each local character. Their map to principal weights is
constructed using the converse proved in `PrincipalConverse`.

Injectivity follows from subgroup separation and the local character
enumeration. Surjectivity uses the FYZ factor exclusion followed by the
inverse of that enumeration on the selected weight's own character. No
source field is a bijection of weights or a principal membership claim.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer
open ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin
open ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource
open ModularRep.PaperProofs.OddTwoFYZCompleteProductSourceJoin
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer

universe u

variable {n : ℕ} {F K : Type u} [Field F] [Fintype F] [Field K] [CharZero K]

local instance parameterSpFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

local instance parameterBasicQuotientFintype (P : ProductShape n F) (i : Fin P.count) :
    Fintype (BasicQuotient P i) := Fintype.ofFinite _

/-- The assumed normaliser description for the specified product. The
centraliser containment is proved using the independent sign proof. -/
structure PrincipalNormalizerData (P : ProductShape n F) (A : P.Geometry) where
  separated : ∀ i j, BasicConjugate P i j → i = j
  normalizerLift : NormalizerWreaths P →*
    Subgroup.normalizer (A.subgroup : Set (Sp n F))
  normalizerLift_matrix : ∀ z,
    ((normalizerLift z).1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.reindex ((groupedCoordinates P).trans A.basisIndex)
        ((groupedCoordinates P).trans A.basisIndex)
          (Matrix.blockDiagonal' (fun i => basicMonomialMatrix P i (z i)))
  quotientEquiv : QuotientWreaths P ≃* NormalizerQuotient A.subgroup
  quotient_square : ∀ z,
    quotientEquiv (quotientWreathMap P z) =
      QuotientGroup.mk' (A.subgroup.subgroupOf
        (Subgroup.normalizer (A.subgroup : Set (Sp n F)))) (normalizerLift z)

/-- Local group and character sources for one actual surviving product.
The arbitrary staircase assignments are not fields of this source. -/
structure PrincipalProductData where
  shape : ProductShape n F
  geometry : shape.Geometry
  basicCentralizers : AnBasicCentralizers shape
  normalizer : PrincipalNormalizerData shape geometry
  localCharacters : ∀ i, BasicModel.LocalEnumeration (K := K) (shape.basic i)
  formula : CoreFormulaData (multiplicity := shape.copies)
    (BasicQuotient shape) (fun i => (localCharacters i).enumeration)
  characters : AnFMCoreCharacterSource (BasicQuotient shape)
    (fun i => (localCharacters i).enumeration) formula

namespace PrincipalProductData

variable (A : PrincipalProductData (n := n) (F := F) (K := K))

/-- The matrix equations for the direct sum imply independent sign separation. -/
theorem signs : IndependentSignSeparation A.shape A.geometry :=
  independentSignSeparation A.shape A.geometry

def normalizerSource (fieldOdd : Odd (Nat.card F)) :
    AnProductNormalizerSource A.shape A.geometry where
  separated := A.normalizer.separated
  normalizerLift := A.normalizer.normalizerLift
  normalizerLift_matrix := A.normalizer.normalizerLift_matrix
  quotientEquiv := A.normalizer.quotientEquiv
  quotient_square := A.normalizer.quotient_square
  centralizer_le := independentProduct_centralizer_le A.shape A.geometry fieldOdd
    A.signs A.basicCentralizers

def enumeration (fieldOdd : Odd (Nat.card F)) : Assignments A.shape ≃
    LocalDefectZeroCharacters (K := K) A.geometry.subgroup :=
  localEnumeration A.shape A.geometry (A.normalizerSource fieldOdd)
    A.localCharacters A.formula A.characters

def pair (fieldOdd : Odd (Nat.card F))
    (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
    (h : Assignments A.shape) : CharacterWeight 2 K (Sp n F) :=
  principalPair core A.geometry.subgroup
    (independentProduct_isPGroup A.shape A.geometry A.basicCentralizers)
    (A.enumeration fieldOdd h)

@[simp] theorem pair_subgroup (fieldOdd : Odd (Nat.card F))
    (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
    (h : Assignments A.shape) :
    (A.pair fieldOdd core h).subgroup = A.geometry.subgroup := rfl

theorem pair_character_on_lift (fieldOdd : Odd (Nat.card F))
    (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
    (h : Assignments A.shape) (z : NormalizerWreaths A.shape) :
    (A.pair fieldOdd core h).localCharacter
      (QuotientGroup.mk' (A.geometry.subgroup.subgroupOf
        (Subgroup.normalizer (A.geometry.subgroup : Set (Sp n F))))
          (A.normalizer.normalizerLift z)) =
      A.formula.characterFunction h (quotientWreathMap A.shape z) :=
  localEnumeration_on_lift A.shape A.geometry (A.normalizerSource fieldOdd)
    A.localCharacters A.formula A.characters h z

end PrincipalProductData

variable {Index : Type u}

/-- The assumed classification of the specified product subgroups. Coverage is
stated for every surviving product geometry, without choosing a principal
weight. Separation concerns conjugacy of subgroups and does not compare
characters. -/
structure PrincipalProductClassification
    (atlas : Index → PrincipalProductData (n := n) (F := F) (K := K)) : Prop where
  separated : ∀ (i j : Index) (g : Sp n F),
    (atlas i).geometry.subgroup.comap (MulAut.conj g⁻¹).toMonoidHom =
      (atlas j).geometry.subgroup → i = j
  exhaustive : ∀ (P : ProductShape n F) (A : P.Geometry),
    ∃ (i : Index) (g : Sp n F),
      A.subgroup.comap (MulAut.conj g⁻¹).toMonoidHom = (atlas i).geometry.subgroup

/-- A staircase is assigned separately to every actual local character. -/
abbrev PrincipalParameter
    (atlas : Index → PrincipalProductData (n := n) (F := F) (K := K)) :=
  Σ i : Index, Assignments (atlas i).shape

section Reconstruction

variable {k Block : Type u} [Field k] [CharP k 2] [IsAlgClosed k]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (fieldOdd : Odd (Nat.card F))
variable (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
variable (criterion : FYZPrincipalCriterion D)
variable (atlas : Index → PrincipalProductData (n := n) (F := F) (K := K))

include criterion in
theorem parameterPair_principal (h : PrincipalParameter atlas) :
    D.blockSource.operations.rawWeightBlock ((atlas h.1).pair fieldOdd core h.2) =
      D.principalBlock :=
  principal_of_centralizer_le D criterion ((atlas h.1).pair fieldOdd core h.2)
    (independentProduct_centralizer_le (atlas h.1).shape (atlas h.1).geometry
      fieldOdd (atlas h.1).signs (atlas h.1).basicCentralizers)

def parameterWeight (h : PrincipalParameter atlas) : D.PrincipalWeight :=
  ⟨Quotient.mk'' (Quotient.mk'' ((atlas h.1).pair fieldOdd core h.2)),
    parameterPair_principal D fieldOdd core criterion atlas h⟩

theorem parameterWeight_injective (classification : PrincipalProductClassification atlas) :
    Function.Injective (parameterWeight D fieldOdd core criterion atlas) := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ heq
  have horbit := congrArg Subtype.val heq
  obtain ⟨g, hg⟩ := Quotient.exact horbit
  have hpair : Isomorphic
      (((atlas j).pair fieldOdd core hj).rightTwist (MulAut.conj g⁻¹))
      ((atlas i).pair fieldOdd core hi) := Quotient.exact hg
  have hji : j = i := classification.separated j i g hpair.1
  subst j
  have hraw := isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
    (Quotient.mk'' ((atlas i).pair fieldOdd core hi))
    (Quotient.mk'' ((atlas i).pair fieldOdd core hj)) horbit rfl
  have hp : Isomorphic ((atlas i).pair fieldOdd core hi)
      ((atlas i).pair fieldOdd core hj) := Quotient.exact hraw
  obtain ⟨hsub, hchar⟩ := hp
  have hcharacter : (atlas i).enumeration fieldOdd hi =
      (atlas i).enumeration fieldOdd hj := by
    apply Subtype.ext
    change castLocalCharacter rfl ((atlas i).enumeration fieldOdd hi).1 =
      ((atlas i).enumeration fieldOdd hj).1 at hchar
    exact hchar
  have hh := ((atlas i).enumeration fieldOdd).injective hcharacter
  cases hh
  rfl

variable (classification : PrincipalProductClassification atlas)
variable (lemma23 : FYZLemma23IntrinsicCertificate D)
/-- The original factor decomposition and the individual published factor
assumptions for a selected principal weight. The surviving product and its
subgroup identity are derived below. -/
structure PrincipalFactorData (w : D.PrincipalWeight) where
  factors : FullFactorData (selectedCharacterWeight D.blockSource D.principalBlock w)
  factorSources : PrincipalFactorSources D w factors

namespace PrincipalFactorData

variable {D} {w : D.PrincipalWeight} (A : PrincipalFactorData D w)

/-- Factor exclusion determines the surviving product from the source data. -/
abbrev shape : ProductShape n F := A.factorSources.productShape fieldOdd lemma23

/-- The product inherits the independent matrix coordinates of the source. -/
abbrev geometry : (A.shape fieldOdd lemma23).Geometry :=
  A.factorSources.productGeometry fieldOdd lemma23

/-- The source subgroup formula and factor exclusion prove the identity for the
selected subgroup. Assumptions on its normaliser or local character are not
required. -/
theorem subgroup_match :
    ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj A.factors.conjugator⁻¹)).subgroup =
        (A.geometry fieldOdd lemma23).subgroup :=
  A.factorSources.subgroup_match fieldOdd lemma23

end PrincipalFactorData

/-- Factor data for each principal weight. The inverse uses the separately
specified enumeration of local characters on the classified products. The
source includes no centraliser containment, selected enumeration or
candidate character. -/
structure PrincipalFactorSelection : Prop where
  selected : ∀ w : D.PrincipalWeight, Nonempty (PrincipalFactorData D w)

namespace PrincipalFactorSelection

variable {D} (S : PrincipalFactorSelection D)

def data (w : D.PrincipalWeight) : PrincipalFactorData D w :=
  Classical.choice (S.selected w)

end PrincipalFactorSelection

variable (factors : PrincipalFactorSelection D)

theorem conjugate_subgroup_trans {G : Type u} [Group G]
    (R S T : Subgroup G) (g h : G)
    (hRS : R.comap (MulAut.conj g⁻¹).toMonoidHom = S)
    (hST : S.comap (MulAut.conj h⁻¹).toMonoidHom = T) :
    R.comap (MulAut.conj (h * g)⁻¹).toMonoidHom = T := by
  rw [mul_inv_rev, map_mul]
  change (R.comap (MulAut.conj g⁻¹).toMonoidHom).comap
    (MulAut.conj h⁻¹).toMonoidHom = T
  rw [hRS, hST]

include fieldOdd classification lemma23 factors in
/-- Factor exclusion and the subgroup classification locate the support of the
selected principal weight among the classified products. -/
theorem selected_subgroup_in_atlas (w : D.PrincipalWeight) :
    ∃ (i : Index) (g : Sp n F),
      ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹)).subgroup = (atlas i).geometry.subgroup := by
  let A := factors.data w
  obtain ⟨i, g, hg⟩ := classification.exhaustive
    (A.shape fieldOdd lemma23) (A.geometry fieldOdd lemma23)
  refine ⟨i, g * A.factors.conjugator, ?_⟩
  exact conjugate_subgroup_trans
    (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup
    (A.geometry fieldOdd lemma23).subgroup (atlas i).geometry.subgroup A.factors.conjugator g
    (A.subgroup_match fieldOdd lemma23) hg

/-- Choose the subgroup coordinates. The inverse enumeration of local characters
then determines its character parameter. -/
def selectedSupport (w : D.PrincipalWeight) :
    Σ i : Index, {g : Sp n F //
      ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹)).subgroup = (atlas i).geometry.subgroup} := by
  let h := selected_subgroup_in_atlas D fieldOdd atlas classification lemma23 factors w
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

def inverseParameter (w : D.PrincipalWeight) : PrincipalParameter atlas :=
  let support := selectedSupport D fieldOdd atlas classification lemma23 factors w
  ⟨support.1, matchingIndex
    (selectedCharacterWeight D.blockSource D.principalBlock w)
    (MulAut.conj support.2.1⁻¹) support.2.2
    ((atlas support.1).enumeration fieldOdd)⟩

theorem parameterWeight_inverse (w : D.PrincipalWeight) :
    parameterWeight D fieldOdd core criterion atlas
      (inverseParameter D fieldOdd atlas classification lemma23 factors w) = w := by
  let support := selectedSupport D fieldOdd atlas classification lemma23 factors w
  let enumeration := (atlas support.1).enumeration fieldOdd
  let h := matchingIndex (selectedCharacterWeight D.blockSource D.principalBlock w)
    (MulAut.conj support.2.1⁻¹) support.2.2 enumeration
  have hpair : (atlas support.1).pair fieldOdd core h =
      selectedEnumeratedPair D w (atlas support.1).geometry.subgroup support.2.1
        support.2.2 enumeration := rfl
  apply Subtype.ext
  change (Quotient.mk'' (Quotient.mk'' ((atlas support.1).pair fieldOdd core h)) :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Sp n F)) = w.1
  rw [hpair]
  exact selectedEnumeratedPair_class D w (atlas support.1).geometry.subgroup
    support.2.1 support.2.2 enumeration

/-- The manuscript's converse and reversible wreath construction give this
equivalence. Its inverse uses the same selected local character. -/
def principalParameterEquiv : PrincipalParameter atlas ≃ D.PrincipalWeight where
  toFun := parameterWeight D fieldOdd core criterion atlas
  invFun := inverseParameter D fieldOdd atlas classification lemma23 factors
  left_inv h := by
    apply parameterWeight_injective D fieldOdd core criterion atlas classification
    exact parameterWeight_inverse D fieldOdd core criterion atlas classification lemma23
      factors (parameterWeight D fieldOdd core criterion atlas h)
  right_inv := parameterWeight_inverse D fieldOdd core criterion atlas classification lemma23
    factors

include fieldOdd core criterion classification lemma23 factors in
/-- The total number of principal weights equals the number of the admissible
core assignments on the classified products. -/
theorem principalParameter_card :
    Nat.card D.PrincipalWeight = Nat.card (PrincipalParameter atlas) :=
  Nat.card_congr
    (principalParameterEquiv D fieldOdd core criterion atlas classification lemma23 factors).symm

end Reconstruction

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
