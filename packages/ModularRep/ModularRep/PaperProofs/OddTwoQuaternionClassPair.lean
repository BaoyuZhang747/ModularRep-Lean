import ModularRep.PaperProofs.OddTwoQuaternionBasicSourceJoin
import ModularRep.PaperProofs.OddTwoLocalUniquenessTransport
import ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

/-!
# The two actual quaternion candidates and their principal pair join

The first candidate is the actual quaternion-wreath pair already constructed.
The second is its actual diagonal image, using the matrix-level nonsquare
similitude from the final-window group data. The inverse in `rightTwist` is
intentional: this right action uses subgroup comap, so the resulting subgroup
is the direct image under the displayed diagonal automorphism.

Only one An local uniqueness input is used. Its companion follows by the
existing normalizer-quotient character transport. Given the source subgroup
conjugacy for either candidate, the actual intrinsic FM principal pair and
its equality with the FYZ weight follow from the checked principal bridge.

The source group-classification input remains separate: An (1G)(b), FYZ
3.48(3) and FM Section 5.1/Lemma 5.1 identify these as the two classes, up to
genuine conjugacy and a possible permutation of alpha names. This file does
not assume either candidate is principal, add a new weight equivalence, or
claim coverage of the exceptional a=2 case or products of basic factors.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoQuaternionClassPair

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoQuaternionBasicSourceJoin
open ModularRep.PaperProofs.OddTwoLocalUniquenessTransport
open ModularRep.PaperProofs.OddTwoQuaternionFactor
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable (C : QuaternionBasicModel n F)
variable (S : AnQuaternionBasicLocalSource (K := K) C)
variable (O : OddTwoFinalBlockOrbitCentralCoverDescentWindow.LiteralDiagonalFieldRealisation n F)

def candidate (i : Fin 2) : CharacterWeight 2 K (Sp n F) :=
  if i = 0 then S.rawPair C else (S.rawPair C).rightTwist O.outer.diagonal.unop⁻¹

theorem candidate_zero : candidate C S O 0 = S.rawPair C := by
  simp [candidate]

theorem candidate_one : candidate C S O 1 =
    (S.rawPair C).rightTwist O.outer.diagonal.unop⁻¹ := by
  simp [candidate]

/-- The companion subgroup is the direct image under the actual displayed
diagonal automorphism, despite the right-action comap convention. -/
theorem candidate_one_subgroup :
    (candidate C S O 1).subgroup =
      C.subgroup.map O.outer.diagonal.unop.toMonoidHom := by
  rw [candidate_one]
  change C.subgroup.comap (O.outer.diagonal.unop⁻¹).toMonoidHom =
    C.subgroup.map O.outer.diagonal.unop.toMonoidHom
  ext x
  constructor
  · intro hx
    exact Subgroup.mem_map.mpr
      ⟨O.outer.diagonal.unop⁻¹ x, hx, O.outer.diagonal.unop.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change O.outer.diagonal.unop⁻¹ (O.outer.diagonal.unop y) ∈ C.subgroup
    simpa using hy

/-- The group-only candidate list is independent of all local characters. -/
def classSubgroup (i : Fin 2) : Subgroup (Sp n F) :=
  if i = 0 then C.subgroup else C.subgroup.map O.outer.diagonal.unop.toMonoidHom

theorem candidate_subgroup (i : Fin 2) :
    (candidate C S O i).subgroup = classSubgroup C O i := by
  fin_cases i
  · simp [candidate, classSubgroup, AnQuaternionBasicLocalSource.rawPair]
  · simpa [classSubgroup] using candidate_one_subgroup C S O

/-- Narrow group-only E2 specialization of An (1G)(b), FYZ's
multiplicity-one/wreath definitions and FM Section 5.1/Lemma 5.1. It covers
every actual quaternion subgroup of the plane, using the same list and
matrix coordinates. The source proof uses faithful irreducibility in
dimension two, the two base classes, and repeated-similitude compatibility.
It contains no character or weight, principal block, or iBAW conclusion.

This field is coverage, not nonconjugacy of the two candidates. In
particular, its type does not silently infer that they are distinct. -/
structure AnQuaternionClassCoverage : Prop where
  covers : ∀ E : Subgroup (FormIsometryGroup (omega (F := F))),
    Nonempty (QuaternionGroup 2 ≃* E) →
      ∃ (i : Fin 2) (g : Sp n F),
        (C.subgroupWithBase E).comap (MulAut.conj g⁻¹).toMonoidHom =
          classSubgroup C O i

/-- The literal single-basic FYZ subgroup formula, up to actual ambient
conjugacy. It does not identify a source alpha name by fiat. In case (3),
FYZ equation (3.34) and the wreath definition supply these group data.
No selected-character comparison or principal claim is stored here. -/
structure SingleQuaternionWreathRealisation (R : Subgroup (Sp n F)) where
  base : Subgroup (FormIsometryGroup (omega (F := F)))
  quaternionType : Nonempty (QuaternionGroup 2 ≃* base)
  conjugator : Sp n F
  subgroup_formula : R.comap (MulAut.conj conjugator⁻¹).toMonoidHom =
    C.subgroupWithBase base

/-- Compose the actual FYZ coordinate conjugacy with the published basic
classification. The resulting candidate match is derived in K. -/
theorem subgroupMatch_of_realisation
    (A : AnQuaternionClassCoverage C O) (R : Subgroup (Sp n F))
    (T : SingleQuaternionWreathRealisation C R) :
    ∃ (i : Fin 2) (g : Sp n F),
      R.comap (MulAut.conj g⁻¹).toMonoidHom = classSubgroup C O i := by
  obtain ⟨i, g, hg⟩ := A.covers T.base T.quaternionType
  refine ⟨i, g * T.conjugator, ?_⟩
  have hcomp : (MulAut.conj (g * T.conjugator)⁻¹).toMonoidHom =
      (MulAut.conj T.conjugator⁻¹).toMonoidHom.comp
        (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.comap_comap, T.subgroup_formula]
  exact hg

/-- Uniqueness for the second actual pair is proved, not cited again. -/
theorem candidate_unique (i : Fin 2) :
    Subsingleton (LocalDefectZeroCharacters (K := K) (candidate C S O i).subgroup) := by
  classical
  by_cases hi : i = 0
  · subst i
    rw [candidate_zero]
    exact S.local_unique
  · simp only [candidate, if_neg hi]
    exact localDefectZero_subsingleton_rightTwist (S.rawPair C)
      O.outer.diagonal.unop⁻¹ S.local_unique

variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (w : D.PrincipalWeight) (i : Fin 2) (g : Sp n F)
variable (hQ : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
  (MulAut.conj g⁻¹)).subgroup = (candidate C S O i).subgroup)

/-- A genuine subgroup-classification match selects the actual principal
pair. Its local character has already been constructed, including on the
diagonal companion, rather than compared by a new source premise. -/
def principalWeight : D.FengMallePrincipalWeight :=
  fengMalleWeightOfConjugateUnique D w (candidate C S O i) g hQ
    (candidate_unique C S O i)

theorem principalWeight_eq :
    principalWeight C S O D w i g hQ = D.intrinsicWeightEquiv w :=
  fengMalleWeightOfConjugateUnique_eq D w (candidate C S O i) g hQ
    (candidate_unique C S O i)

include C S O D w i g hQ in
theorem candidate_principalBlock :
    D.blockSource.operations.rawWeightBlock (candidate C S O i) = D.principalBlock :=
  conjugateUniquePair_principalBlock D w (candidate C S O i) g hQ
    (candidate_unique C S O i)

include C S O D w i g hQ in
theorem candidate_blockInducesTo :
    let V := candidate C S O i
    let B := D.blockSource.operations
    let localData := B.inflatedNormalizerBlockData V.subgroup
    letI := B.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue B.ambientBlockData.catalogue
      (B.inflateToNormalizer V.subgroup
        (B.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      D.principalBlock :=
  conjugateUniquePair_blockInducesTo D w (candidate C S O i) g hQ
    (candidate_unique C S O i)

/-- For an actual single-basic FYZ weight, the group-only source input now
produces the match consumed by the principal weight bridge. This does not
assume the subgroup match directly, or principal membership of a candidate.
Its displayed equality is in the actual common intrinsic weight fibre. -/
theorem exists_principalPair_of_realisation
    (A : AnQuaternionClassCoverage C O)
    (T : SingleQuaternionWreathRealisation C
      (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup) :
    ∃ (i : Fin 2) (g : Sp n F)
      (h : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹)).subgroup = (candidate C S O i).subgroup),
      principalWeight C S O D w i g h = D.intrinsicWeightEquiv w := by
  obtain ⟨i, g, hg⟩ := subgroupMatch_of_realisation C O A _ T
  have h : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj g⁻¹)).subgroup = (candidate C S O i).subgroup := by
    rw [candidate_subgroup]
    exact hg
  exact ⟨i, g, h, principalWeight_eq C S O D w i g h⟩

end ModularRep.PaperProofs.OddTwoQuaternionClassPair


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
