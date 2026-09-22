import ModularRep.PaperProofs.OddTwoAmbientRealisation

/-!
# Source adapter for the corrected even multiplicity family

Feng--Yu--Zhang use two different levels of the index `alpha` in the
construction relevant to Proposition 3.3.  On printed pp. 28--29 of arXiv
2401.00156v4 they first choose representatives `R^0_{0,gamma}` and, when
there are two classes, `R^0_{1,gamma}`.  For `i = 0`, `alpha = 1`, and even
`m`, equation (3.35) then defines `R^0_{m,1,gamma}` using the right tensor
embedding

`R^{0,eta}_{0,gamma} -> I(W tensor V^0_{0,gamma}),  g |-> I_m tensor g`.

Thus the affected full factor has index `alpha = 1`, but the right tensor
factor in its definition is the source-labelled `alpha = 0` representative.
When `a >= 3` there are two possible right-factor conjugacy classes, so an
arbitrary concrete quaternion copy cannot silently be identified with the
required `R^{0,-}_{0,1}` representative.

This file makes that distinction visible in the types.  It also removes a
purely formal source-to-Lean gap: the copy of the abstract centre `Z(R)` in
`C_G(R)` is proved to equal `centreInCentralizer R`.  The strongest endpoint
therefore consumes Feng--Yu--Zhang, Lemma 2.3, in its literal Sylow-centre
form.  It does not assume a larger `2`-subgroup, the failure of the Sylow
condition, or the desired principal-weight exclusion.

The remaining source input is explicit.  Equation (3.35) itself supplies the
particular `R^{0,-}_{0,1}` right factor and defines the full factor by the
right tensor map.  Theorem 3.37 supplies the orthogonal direct-product
decomposition up to conjugacy, and Proposition 3.48 gives the permitted
factors for a weight subgroup.  These are exact E2 source data, not an
unmatched carrier and not theorems reconstructed here.  Passing to a diagonal
Gram matrix and transporting the direct sum by a change of basis are routine
E1 linear algebra under `SF-ODD-ORTHOGONAL-COORDINATES` and
`SF-SYMPLECTIC-COORDINATES`.  The negative
orthogonal form and reflection are routine E1 geometry under
`SF-ORTHOGONAL-REFLECTION`.  Neither E1 input receives manuscript-specific K
credit.
-/

namespace ModularRep.PaperProofs.OddTwoFYZSourceAdapter

open ModularRep.PaperProofs.OddTwoAmbientRealisation
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.OddTwoQuaternionFactor
open ModularRep.PaperProofs.OddTwoSourceWreathAction
open ModularRep.PaperProofs.OddTwoWreathReflection

universe u v

/-! ## The two source indices -/

/-- Labels for the two isometry-group conjugacy classes allowed in the
source when its parameter `a` is at least three.  This is only a source label:
placing a subgroup in `FYZRightFactor .zero` does not prove the corresponding
conjugacy class assertion. -/
inductive FYZClassIndex where
  | zero
  | one
  deriving DecidableEq, Repr

/-- The index on the full corrected family `R^{0,-}_{m,1,1,c}`. -/
def correctedFamilyIndex : FYZClassIndex := .one

/-- The index of the right tensor factor actually used in equation (3.35). -/
def correctedRightFactorIndex : FYZClassIndex := .zero

theorem correctedRightFactorIndex_ne_correctedFamilyIndex :
    correctedRightFactorIndex ≠ correctedFamilyIndex := by
  decide

/-- A subgroup tagged by the source conjugacy class index it is intended to
represent.  The tag records the remaining source obligation but does not
manufacture a proof that the subgroup lies in that class. -/
structure FYZRightFactor
    (classIndex : FYZClassIndex)
    (F : Type u) [Field F] where
  subgroup : Subgroup (FormIsometryGroup (omega (F := F)))

/-- Equation (3.35) requires the source-labelled class `alpha = 0`, even
though the resulting full factor has index `alpha = 1`. -/
abbrev FYZAlphaZeroRightFactor (F : Type u) [Field F] :=
  FYZRightFactor .zero F

/-! ## The literal copy of `Z(R)` in `C_G(R)` -/

section CentreAdapter

variable {G : Type u} [Group G]

/-- Embed the abstract centre of the subgroup `R` into its ambient
centraliser. -/
def subgroupCentreEmbedding (R : Subgroup G) :
    Subgroup.center R →* Subgroup.centralizer (R : Set G) where
  toFun z := by
    refine ⟨z.1.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hz : ∀ x : R, x * z.1 = z.1 * x :=
      Subgroup.mem_center_iff.mp z.2
    exact congrArg Subtype.val (hz ⟨r, hr⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The source notation `Z(R) <= C_G(R)`, expressed as the range of the
literal centre embedding. -/
def sourceCentreInCentralizer (R : Subgroup G) :
    Subgroup (Subgroup.centralizer (R : Set G)) :=
  (subgroupCentreEmbedding R).range

/-- The range of the literal embedding of `Z(R)` is exactly the subgroup
`centreInCentralizer R` used by the checked Sylow obstruction. -/
theorem sourceCentreInCentralizer_eq_centreInCentralizer (R : Subgroup G) :
    sourceCentreInCentralizer R = centreInCentralizer R := by
  ext z
  constructor
  · rintro ⟨c, _, rfl⟩
    exact c.1.2
  · intro hz
    let r : R := ⟨z.1, hz⟩
    have hrCenter : r ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact z.2 x.1 x.2
    let c : Subgroup.center R := ⟨r, hrCenter⟩
    refine ⟨c, ?_⟩
    rfl

/-- The precise Sylow-centre implication supplied by the necessary direction
of Feng--Yu--Zhang, Lemma 2.3.  The centre is written in the source form,
rather than already as the target used by the Lean obstruction. -/
def FYZPrincipalCentreSylowClause
    (R : Subgroup G) (IsPrincipalWeight : Prop) : Prop :=
  IsPrincipalWeight ->
    ∃ P : Sylow 2 (Subgroup.centralizer (R : Set G)),
      (P : Subgroup (Subgroup.centralizer (R : Set G))) =
        sourceCentreInCentralizer R

/-- Convert the literal source form of the Sylow-centre clause to the typed
premise consumed by the ambient exclusion theorem. -/
theorem principalCentreSylow_of_FYZClause
    (R : Subgroup G) (IsPrincipalWeight : Prop)
    (hSource : FYZPrincipalCentreSylowClause R IsPrincipalWeight) :
    IsPrincipalWeight →
      ∃ P : Sylow 2 (Subgroup.centralizer (R : Set G)),
        (P : Subgroup (Subgroup.centralizer (R : Set G))) =
          centreInCentralizer R := by
  intro hPrincipal
  obtain ⟨P, hP⟩ := hSource hPrincipal
  exact ⟨P, hP.trans (sourceCentreInCentralizer_eq_centreInCentralizer R)⟩

end CentreAdapter

/-! ## Source-labelled ambient model -/

section SourceModel

variable {F : Type u} [Field F] [Finite F]
variable {Rest : Type v} [Fintype Rest] [DecidableEq Rest]

noncomputable local instance sourceWreathPointsFintype (cs : List Nat) :
    Fintype (SourceWreathPoints cs) := Fintype.ofFinite _

noncomputable local instance sourceWreathPointsDecidableEq (cs : List Nat) :
    DecidableEq (SourceWreathPoints cs) := Classical.decEq _

/-- Source data which are genuinely prior to the reflection argument.

The evenness field records the range of Proposition 3.48(4).  The right
factor is tagged `alpha = 0`, as required by equation (3.35).  The remaining
subgroup and conjugator encode the orthogonal decomposition and the fact that
the classification specifies the radical subgroup only up to conjugacy.
There is deliberately no independent `Rsource` and no conjugacy equality
hypothesis shaped like a later conclusion. -/
structure FYZCorrectedSourceModel
    (n : Nat) (cs : List Nat) (d : Fin (n + 2) → F)
    (K : Matrix Rest Rest F) where
  multiplicity_even : Even (n + 2)
  rightFactor : FYZAlphaZeroRightFactor F
  remainingSubgroup : Subgroup (FormIsometryGroup K)
  conjugator : FormIsometryGroup (correctedFullGram n cs d K)

/-- The source representative determined by the supplied equation (3.35)
factor, remaining direct factors, and classification conjugator. -/
noncomputable def FYZCorrectedSourceModel.subgroup
    {n : Nat} {cs : List Nat} {d : Fin (n + 2) → F}
    {K : Matrix Rest Rest F}
    (D : FYZCorrectedSourceModel n cs d K) :
    Subgroup (FormIsometryGroup (correctedFullGram n cs d K)) :=
  (correctedFullSubgroupWithFactor n cs d D.rightFactor.subgroup K
      D.remainingSubgroup).map
    (MulAut.conj D.conjugator).toMonoidHom

omit [Finite F] in
/-- The excluding reflection for the source-labelled model is constructed
internally and transported by the supplied classification conjugator. -/
theorem FYZCorrectedSourceModel.reflection_involution_centralises_outside
    (hTwo : (2 : F) ≠ 0)
    {n : Nat} {cs : List Nat} {d : Fin (n + 2) → F}
    {K : Matrix Rest Rest F}
    (D : FYZCorrectedSourceModel n cs d K) :
    let T := (MulAut.conj D.conjugator)
      (canonicalCorrectedFullReflection n cs d K)
    T ^ 2 = 1 ∧
      T ∈ Subgroup.centralizer (D.subgroup : Set _) ∧ T ∉ D.subgroup := by
  exact sourceConjugate_correctedFullReflection_involution_centralises_outside
    hTwo n cs d D.rightFactor.subgroup K D.remainingSubgroup D.subgroup
      D.conjugator rfl

omit [Finite F] in
/-- Strongest honest principal-weight exclusion for the source-labelled
model.  The only representation theoretic premise is the literal necessary
Sylow-centre clause of Feng--Yu--Zhang, Lemma 2.3. -/
theorem FYZCorrectedSourceModel.not_principal
    (hTwo : (2 : F) ≠ 0)
    {n : Nat} {cs : List Nat} {d : Fin (n + 2) → F}
    {K : Matrix Rest Rest F}
    (D : FYZCorrectedSourceModel n cs d K)
    (IsPrincipalWeight : Prop)
    (hFYZ : FYZPrincipalCentreSylowClause D.subgroup IsPrincipalWeight) :
    ¬ IsPrincipalWeight := by
  exact sourceConjugate_correctedFullFactor_not_principal
    hTwo n cs d D.rightFactor.subgroup K D.remainingSubgroup D.subgroup
      D.conjugator rfl IsPrincipalWeight
      (principalCentreSylow_of_FYZClause D.subgroup IsPrincipalWeight hFYZ)

end SourceModel

/-! ## Direct instantiation of equation (3.35) and Proposition 3.48 -/

section Equation335Instantiation

variable {F : Type u} [Field F] [Finite F]
variable {Rest : Type v} [Fintype Rest] [DecidableEq Rest]

noncomputable local instance sourceWreathPointsFintypeEquation335
    (cs : List Nat) : Fintype (SourceWreathPoints cs) := Fintype.ofFinite _

noncomputable local instance sourceWreathPointsDecidableEqEquation335
    (cs : List Nat) : DecidableEq (SourceWreathPoints cs) := Classical.decEq _

/-- The exact source carrier used in the affected case of Proposition 3.48.

`equation335RightFactor` is the source's named `R^{0,-}_{0,1}` factor, not an
arbitrary quaternion subgroup.  Equation (3.35) maps it by
`g |-> I_m tensor g`; `correctedFullSubgroupWithFactor` implements that map
and the subsequent wreath product.  `remainingSubgroup` and
`classificationConjugator` are the other direct factors and the conjugacy
supplied by Theorem 3.37 and the factor list in Proposition 3.48.  The record
contains no principal-weight exclusion, Sylow
failure, larger `2`-subgroup, BAW-goodness, or iBAW assertion. -/
structure FYZEquation335Decomposition
    (n : Nat) (cs : List Nat) (d : Fin (n + 2) → F)
    (K : Matrix Rest Rest F) where
  multiplicity_even : Even (n + 2)
  equation335RightFactor : FYZAlphaZeroRightFactor F
  remainingSubgroup : Subgroup (FormIsometryGroup K)
  classificationConjugator : FormIsometryGroup (correctedFullGram n cs d K)

/-- Forget the equation-numbered source packaging and retain the geometric
data consumed by the kernel-checked reflection argument. -/
noncomputable def FYZEquation335Decomposition.toCorrectedSourceModel
    {n : Nat} {cs : List Nat} {d : Fin (n + 2) → F}
    {K : Matrix Rest Rest F}
    (D : FYZEquation335Decomposition n cs d K) :
    FYZCorrectedSourceModel n cs d K where
  multiplicity_even := D.multiplicity_even
  rightFactor := D.equation335RightFactor
  remainingSubgroup := D.remainingSubgroup
  conjugator := D.classificationConjugator

/-- The full corrected subgroup defined from equation (3.35), the source
wreath factor, and the direct-product decomposition in Theorem 3.37 with the
factor list in Proposition 3.48. -/
noncomputable def FYZEquation335Decomposition.subgroup
    {n : Nat} {cs : List Nat} {d : Fin (n + 2) → F}
    {K : Matrix Rest Rest F}
    (D : FYZEquation335Decomposition n cs d K) :
    Subgroup (FormIsometryGroup (correctedFullGram n cs d K)) :=
  D.toCorrectedSourceModel.subgroup

omit [Finite F] in
/-- Source-instantiated exclusion of the even-multiplicity factor from a
principal weight.  The source inputs are exactly equation (3.35), the
decomposition in Theorem 3.37 and Proposition 3.48, and the necessary
Sylow-centre condition from Lemma 2.3.  All deductions after those inputs are
kernel checked. -/
theorem equation335_source_instantiated_principal_exclusion
    (hTwo : (2 : F) ≠ 0)
    {n : Nat} {cs : List Nat} {d : Fin (n + 2) → F}
    {K : Matrix Rest Rest F}
    (D : FYZEquation335Decomposition n cs d K)
    (IsPrincipalWeight : Prop)
    (hLemma23 : FYZPrincipalCentreSylowClause D.subgroup IsPrincipalWeight) :
    ¬ IsPrincipalWeight := by
  exact D.toCorrectedSourceModel.not_principal hTwo IsPrincipalWeight hLemma23

end Equation335Instantiation

end ModularRep.PaperProofs.OddTwoFYZSourceAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
