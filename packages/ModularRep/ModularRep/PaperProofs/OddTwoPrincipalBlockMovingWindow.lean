import ModularRep.PaperProofs.OddTwoFYZSourceAdapter
import ModularRep.PaperProofs.OddTwoPrincipalParameterElimination
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions

/-!
# A corrected principal-block moving window for Proposition 3.3

This module stops strictly below Proposition 3.3 and below every assertion
that a block is BAW-good or that an iBAW condition holds.  Its output consists
of carriers, actions, an equivariant equivalence, literal principal-block
facts, and the two correction exclusions needed before the principal fibre of
Feng--Malle can be used.

The proof boundary is the following.

* **K.**  `FengMallePrincipalBlockCorrespondence` transports the equivalence
  of Feng--Malle, Theorem 6.2, across explicit carrier identifications.
  `correctedNonXLocalFactor_isEmpty` maps every *actual* corrected local
  factor to
  `OddTwoPrincipalParameterElimination.NonXLocalContribution` and invokes the
  already checked emptiness theorem.  `fyzOmittedEvenOccurrence_isEmpty`
  invokes
  `OddTwoFYZSourceAdapter.equation335_source_instantiated_principal_exclusion`;
  no reflection, wreath, centraliser, or Sylow calculation is repeated here.
* **E1.**  The inherited equation-(3.35) endpoint starts after the coordinate
  changes `SF-ODD-ORTHOGONAL-COORDINATES` and
  `SF-SYMPLECTIC-COORDINATES`, and after the reflection input
  `SF-ORTHOGONAL-REFLECTION`, with exactly the ranges and exceptions recorded
  by the inherited source interfaces. These facts receive no K credit here.
* **E2.**  The source certificates below are theorem-granular: Feng--Malle,
  Corollary 4.3, Proposition 5.4, Proposition 5.9, and Theorem 6.2; and the
  used FYZ clauses from Lemma 2.3, equation (3.35), Theorem 3.37,
  Proposition 3.48(3)--(4) and its proof, and Remarks 3.36 and 3.49--3.50.
  The surviving multiplicity-one case is separately tied to An (4F)(b) and
  Feng--Malle, Section 5.1.  Remark 3.50 is not accepted as the desired
  exclusion, and Remark 3.49 is not treated as a repaired general
  block-label theorem.
* **U.**  `RestrictedCorrectedPrincipalFibreAdapter` is the deliberately
  visible unresolved bridge between corrected principal weights and the
  Feng--Malle principal carrier.  It separately identifies radicals (hence
  normalisers), local defect-zero characters, induced blocks, local factors,
  and the automorphism action.  Covering lifts, central-kernel descent,
  compatible extensions, intermediate blocks, character triples, the use of
  Feng--Malle Proposition 3.4/Remark 3.5, all-block aggregation, and final
  iBAW remain outside this module.  The one local Definition 3.5
  modular-character-triple relation is isolated pointwise in
  `PrincipalSpDefinition35LocalSource`; only after that exact U/E2 relation is
  supplied does Lean package the fixed carrier as `Definition35IBAWBijection`.

In particular, none of the source structures below contains Proposition 3.3,
all-block BAW-goodness, final iBAW, `CharacterTripleOK`, or an equivalent
target predicate.  The `.zero` tag on `FYZRightFactor` is never used as proof
of source identification: `FYZEquation335Certificate` has a separate named
class predicate supplied by the source interpretation.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalBlockMovingWindow

open ModularRep.PaperProofs.OddTwoAmbientRealisation
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.OddTwoFYZSourceAdapter
open ModularRep.PaperProofs.OddTwoPrincipalParameterElimination
open ModularRep.PaperProofs.OddTwoQuaternionFactor
open ModularRep.PaperProofs.OddTwoSourceWreathAction
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-! ## Exact Feng--Malle source carriers -/

section FengMalleSources

variable {A FMBrauer FMWeight ULabel TLabel : Type u}
variable [Group A] [MulAction A FMBrauer] [MulAction A FMWeight]

/-- Pointwise invariance under the indicated subgroup of automorphisms. -/
def FixedBy (H : Subgroup A) {X : Type u} [MulAction A X] (x : X) : Prop :=
  ∀ a, a ∈ H → a • x = x

/-- The two clauses of Feng--Malle, Corollary 4.3, on its own set of Brauer characters
in the principal block and labelling set. -/
structure FengMalleCorollary43Certificate
    (fieldAutomorphisms diagonalAutomorphisms : Subgroup A)
    (isUOne : ULabel → Prop) where
  label : FMBrauer ≃ ULabel
  field_fixed : ∀ chi : FMBrauer, FixedBy fieldAutomorphisms chi
  diagonal_fixed_iff : ∀ chi : FMBrauer,
    FixedBy diagonalAutomorphisms chi ↔ isUOne (label chi)

/-- The two clauses of Feng--Malle, Proposition 5.9, on its own principal
set of weights and labelling set. -/
structure FengMalleProposition59Certificate
    (fieldAutomorphisms diagonalAutomorphisms : Subgroup A)
    (isTOne : TLabel → Prop) where
  label : FMWeight ≃ TLabel
  field_fixed : ∀ weight : FMWeight, FixedBy fieldAutomorphisms weight
  diagonal_fixed_iff : ∀ weight : FMWeight,
    FixedBy diagonalAutomorphisms weight ↔ isTOne (label weight)

/-- Exactly Feng--Malle, Theorem 6.2: the principal-fibre equivalence and its
full automorphism equivariance. -/
structure FengMalleTheorem62Certificate where
  sourceEquiv : FMBrauer ≃ FMWeight
  sourceEquivariant : ∀ (a : A) (chi : FMBrauer),
    sourceEquiv (a • chi) = a • sourceEquiv chi

end FengMalleSources

/-! ## Concrete principal carriers and the restricted unresolved adapter -/

section CarrierSemantics

variable {G A Brauer FMBrauer CorrectedWeight FMWeight : Type u}
variable {CorrectedLocalCharacter FMLocalCharacter Block : Type u}
variable [Group G] [Group A]
variable [MulAction A Brauer] [MulAction A FMBrauer]
variable [MulAction A CorrectedWeight] [MulAction A FMWeight]

/-- Literal block membership for the chosen set of Brauer characters. -/
structure PrincipalBrauerRealisation
    (principalBlock : Block) where
  blockOf : Brauer → Block
  block_eq_principal : ∀ chi, blockOf chi = principalBlock

/-- Concrete data attached to each weight representative.  The character
domain equality makes the displayed subgroup the actual normaliser, and the
last two fields record local defect zero and induction to the principal
block. -/
structure PrincipalWeightRealisation
    (Weight LocalCharacter : Type u) (principalBlock : Block) where
  radical : Weight → Subgroup G
  localCharacter : Weight → LocalCharacter
  characterDomain : LocalCharacter → Subgroup G
  characterDomain_eq_normalizer : ∀ weight,
    characterDomain (localCharacter weight) =
      Subgroup.normalizer (radical weight)
  IsDefectZero : LocalCharacter → Prop
  localCharacter_defectZero : ∀ weight, IsDefectZero (localCharacter weight)
  inducedBlock : LocalCharacter → Block
  inducedBlock_eq_principal : ∀ weight,
    inducedBlock (localCharacter weight) = principalBlock

/-- Only local characters actually attached to weights belong to the
restricted comparison domain.  No comparison of unrelated ambient local
characters is required. -/
def PrincipalWeightRealisation.SelectedLocalCharacter
    {Weight LocalCharacter : Type u} {principalBlock : Block}
    (R : PrincipalWeightRealisation (G := G) Weight LocalCharacter principalBlock) :=
  { character : LocalCharacter // ∃ weight, R.localCharacter weight = character }

def PrincipalWeightRealisation.selectedLocalCharacter
    {Weight LocalCharacter : Type u} {principalBlock : Block}
    (R : PrincipalWeightRealisation (G := G) Weight LocalCharacter principalBlock)
    (weight : Weight) : R.SelectedLocalCharacter :=
  ⟨R.localCharacter weight, weight, rfl⟩

/-- A local-factor carrier belonging to actual weight representatives.  The
amount is the positive contribution appearing in the Proposition 5.4
assignment; `multiplicity` and `multiplicityCentralizer` are kept separate
because the corrected FYZ formula concerns those data, not the partition
amount. -/
structure PrincipalLocalFactorSystem
    (Weight Factor Gamma MultiplicityCentralizer : Type u)
    [Group MultiplicityCentralizer] where
  owner : Factor → Weight
  elementaryDivisor : Factor → Gamma
  amount : Factor → Nat
  multiplicity : Factor → Nat
  multiplicityCentralizer : Factor → Subgroup MultiplicityCentralizer
  IsRZero : Factor → Prop
  minusIdentity : MultiplicityCentralizer

/-- The principal Brauer carrier identification.  This bridge contains no
weight or iBAW statement. -/
structure FengMallePrincipalBrauerCarrierAdapter where
  toFengMalle : Brauer ≃ FMBrauer
  equivariant : ∀ (a : A) (chi : Brauer),
    toFengMalle (a • chi) = a • toFengMalle chi

variable {Gamma CorrectedFactor FMFactor MultiplicityCentralizer : Type u}
variable [Group MultiplicityCentralizer]
variable (principalBlock : Block)
variable
  (Corrected : PrincipalWeightRealisation
    (G := G) CorrectedWeight CorrectedLocalCharacter principalBlock)
  (FM : PrincipalWeightRealisation
    (G := G) FMWeight FMLocalCharacter principalBlock)
  (CorrectedFactors : PrincipalLocalFactorSystem
    CorrectedWeight CorrectedFactor Gamma MultiplicityCentralizer)
  (FMFactors : PrincipalLocalFactorSystem
    FMWeight FMFactor Gamma MultiplicityCentralizer)

/-- The essential restricted corrected-principal-fibre boundary.

No cited FYZ remark or An's unaffected list supplies this structure.  It must
identify the corrected weights with the exact set of weights used in
Feng--Malle, and it records the required compatibilities one by one. -/
structure RestrictedCorrectedPrincipalFibreAdapter where
  weightEquiv : CorrectedWeight ≃ FMWeight
  weightEquivariant : ∀ (a : A) (weight : CorrectedWeight),
    weightEquiv (a • weight) = a • weightEquiv weight
  localCharacterMap : Corrected.SelectedLocalCharacter → FM.SelectedLocalCharacter
  radical_preserved : ∀ weight,
    FM.radical (weightEquiv weight) = Corrected.radical weight
  localCharacter_preserved : ∀ weight,
    localCharacterMap (Corrected.selectedLocalCharacter weight) =
      FM.selectedLocalCharacter (weightEquiv weight)
  factorEquiv : CorrectedFactor ≃ FMFactor
  factor_owner_preserved : ∀ factor,
    weightEquiv (CorrectedFactors.owner factor) =
      FMFactors.owner (factorEquiv factor)
  factor_elementaryDivisor_preserved : ∀ factor,
    FMFactors.elementaryDivisor (factorEquiv factor) =
      CorrectedFactors.elementaryDivisor factor
  factor_amount_preserved : ∀ factor,
    FMFactors.amount (factorEquiv factor) = CorrectedFactors.amount factor
  factor_multiplicity_preserved : ∀ factor,
    FMFactors.multiplicity (factorEquiv factor) =
      CorrectedFactors.multiplicity factor
  factor_centralizer_preserved : ∀ factor,
    FMFactors.multiplicityCentralizer (factorEquiv factor) =
      CorrectedFactors.multiplicityCentralizer factor
  factor_rZero_preserved : ∀ factor,
    FMFactors.IsRZero (factorEquiv factor) ↔ CorrectedFactors.IsRZero factor
  minusIdentity_preserved :
    FMFactors.minusIdentity = CorrectedFactors.minusIdentity

/-- Defect-zero preservation is needed only for the selected characters;
it follows from their literal realization and the selected-character map. -/
theorem RestrictedCorrectedPrincipalFibreAdapter.defectZero_preserved
    (Adapter : RestrictedCorrectedPrincipalFibreAdapter
      (A := A) principalBlock Corrected FM CorrectedFactors FMFactors)
    (weight : CorrectedWeight) :
    Corrected.IsDefectZero (Corrected.localCharacter weight) ↔
      FM.IsDefectZero
        (Adapter.localCharacterMap (Corrected.selectedLocalCharacter weight)).1 := by
  rw [Adapter.localCharacter_preserved]
  exact iff_of_true (Corrected.localCharacter_defectZero weight)
    (FM.localCharacter_defectZero (Adapter.weightEquiv weight))

/-- Induction of the selected local character is preserved; both actual
weight realizations induce to the same specified principal block. -/
theorem RestrictedCorrectedPrincipalFibreAdapter.blockInduction_preserved
    (Adapter : RestrictedCorrectedPrincipalFibreAdapter
      (A := A) principalBlock Corrected FM CorrectedFactors FMFactors)
    (weight : CorrectedWeight) :
    FM.inducedBlock
        (Adapter.localCharacterMap (Corrected.selectedLocalCharacter weight)).1 =
      Corrected.inducedBlock (Corrected.localCharacter weight) := by
  rw [Adapter.localCharacter_preserved]
  exact (FM.inducedBlock_eq_principal (Adapter.weightEquiv weight)).trans
    (Corrected.inducedBlock_eq_principal weight).symm

/-- Normaliser preservation is a K consequence of preservation of the
radical subgroup; it is not an additional source field. -/
theorem RestrictedCorrectedPrincipalFibreAdapter.normalizer_preserved
    (Adapter : RestrictedCorrectedPrincipalFibreAdapter
      (A := A) principalBlock Corrected FM CorrectedFactors FMFactors)
    (weight : CorrectedWeight) :
    Subgroup.normalizer (FM.radical (Adapter.weightEquiv weight) : Set G) =
      Subgroup.normalizer (Corrected.radical weight : Set G) := by
  rw [Adapter.radical_preserved]

end CarrierSemantics

/-! ## Transport of Corollary 4.3, Proposition 5.9, and Theorem 6.2 -/

section CorrespondenceTransport

variable {A Brauer FMBrauer CorrectedWeight FMWeight ULabel TLabel : Type u}
variable [Group A]
variable [MulAction A Brauer] [MulAction A FMBrauer]
variable [MulAction A CorrectedWeight] [MulAction A FMWeight]
variable (fieldAutomorphisms diagonalAutomorphisms : Subgroup A)
variable (isUOne : ULabel → Prop) (isTOne : TLabel → Prop)

theorem fixedBy_iff_of_equivariant_equiv
    {X Y : Type u} [MulAction A X] [MulAction A Y]
    (H : Subgroup A) (e : X ≃ Y)
    (he : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (x : X) : FixedBy H x ↔ FixedBy H (e x) := by
  constructor
  · intro hx a ha
    rw [← he]
    exact congrArg e (hx a ha)
  · intro hx a ha
    apply e.injective
    rw [he]
    exact hx a ha

/-- The actual corrected principal-block equivalence obtained by transporting
the exact Theorem 6.2 equivalence through the two explicit carrier bridges. -/
def correctedPrincipalEquiv
    (BrauerAdapter : FengMallePrincipalBrauerCarrierAdapter
      (A := A) (Brauer := Brauer) (FMBrauer := FMBrauer))
    (Theorem62 : FengMalleTheorem62Certificate
      (A := A) (FMBrauer := FMBrauer) (FMWeight := FMWeight))
    (WeightAdapter : CorrectedWeight ≃ FMWeight) :
    Brauer ≃ CorrectedWeight :=
  (BrauerAdapter.toFengMalle.trans Theorem62.sourceEquiv).trans
    WeightAdapter.symm

theorem correctedPrincipalEquiv_equivariant
    (BrauerAdapter : FengMallePrincipalBrauerCarrierAdapter
      (A := A) (Brauer := Brauer) (FMBrauer := FMBrauer))
    (Theorem62 : FengMalleTheorem62Certificate
      (A := A) (FMBrauer := FMBrauer) (FMWeight := FMWeight))
    (WeightAdapter : CorrectedWeight ≃ FMWeight)
    (hWeight : ∀ (a : A) (weight : CorrectedWeight),
      WeightAdapter (a • weight) = a • WeightAdapter weight)
    (a : A) (chi : Brauer) :
    correctedPrincipalEquiv BrauerAdapter Theorem62 WeightAdapter (a • chi) =
      a • correctedPrincipalEquiv BrauerAdapter Theorem62 WeightAdapter chi := by
  apply WeightAdapter.injective
  simp only [correctedPrincipalEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [BrauerAdapter.equivariant, Theorem62.sourceEquivariant, hWeight]
  simp

/-- The Corollary 4.3 labels on the concrete Brauer carrier. -/
def correctedBrauerLabel
    (BrauerAdapter : FengMallePrincipalBrauerCarrierAdapter
      (A := A) (Brauer := Brauer) (FMBrauer := FMBrauer))
    (Corollary43 : FengMalleCorollary43Certificate
      (A := A) (FMBrauer := FMBrauer)
      (fieldAutomorphisms := fieldAutomorphisms)
      (diagonalAutomorphisms := diagonalAutomorphisms)
      isUOne) : Brauer ≃ ULabel :=
  BrauerAdapter.toFengMalle.trans Corollary43.label

/-- The Proposition 5.9 labels on the corrected set of weights, conditional
on the explicit restricted corrected-principal-fibre adapter. -/
def correctedWeightLabel
    (WeightAdapter : CorrectedWeight ≃ FMWeight)
    (Proposition59 : FengMalleProposition59Certificate
      (A := A) (FMWeight := FMWeight)
      (fieldAutomorphisms := fieldAutomorphisms)
      (diagonalAutomorphisms := diagonalAutomorphisms)
      isTOne) : CorrectedWeight ≃ TLabel :=
  WeightAdapter.trans Proposition59.label

theorem correctedBrauer_field_fixed
    (BrauerAdapter : FengMallePrincipalBrauerCarrierAdapter
      (A := A) (Brauer := Brauer) (FMBrauer := FMBrauer))
    (Corollary43 : FengMalleCorollary43Certificate
      (A := A) (FMBrauer := FMBrauer)
      fieldAutomorphisms diagonalAutomorphisms isUOne)
    (chi : Brauer) : FixedBy fieldAutomorphisms chi := by
  exact (fixedBy_iff_of_equivariant_equiv fieldAutomorphisms
    BrauerAdapter.toFengMalle BrauerAdapter.equivariant chi).mpr
      (Corollary43.field_fixed _)

theorem correctedBrauer_diagonal_fixed_iff
    (BrauerAdapter : FengMallePrincipalBrauerCarrierAdapter
      (A := A) (Brauer := Brauer) (FMBrauer := FMBrauer))
    (Corollary43 : FengMalleCorollary43Certificate
      (A := A) (FMBrauer := FMBrauer)
      fieldAutomorphisms diagonalAutomorphisms isUOne)
    (chi : Brauer) :
    FixedBy diagonalAutomorphisms chi ↔
      isUOne (correctedBrauerLabel fieldAutomorphisms
        diagonalAutomorphisms isUOne BrauerAdapter Corollary43 chi) := by
  rw [fixedBy_iff_of_equivariant_equiv diagonalAutomorphisms
    BrauerAdapter.toFengMalle BrauerAdapter.equivariant chi]
  change FixedBy diagonalAutomorphisms (BrauerAdapter.toFengMalle chi) ↔ _
  exact Corollary43.diagonal_fixed_iff _

theorem correctedWeight_field_fixed
    (WeightAdapter : CorrectedWeight ≃ FMWeight)
    (hWeight : ∀ (a : A) (weight : CorrectedWeight),
      WeightAdapter (a • weight) = a • WeightAdapter weight)
    (Proposition59 : FengMalleProposition59Certificate
      (A := A) (FMWeight := FMWeight)
      fieldAutomorphisms diagonalAutomorphisms isTOne)
    (weight : CorrectedWeight) : FixedBy fieldAutomorphisms weight := by
  exact (fixedBy_iff_of_equivariant_equiv fieldAutomorphisms
    WeightAdapter hWeight weight).mpr (Proposition59.field_fixed _)

theorem correctedWeight_diagonal_fixed_iff
    (WeightAdapter : CorrectedWeight ≃ FMWeight)
    (hWeight : ∀ (a : A) (weight : CorrectedWeight),
      WeightAdapter (a • weight) = a • WeightAdapter weight)
    (Proposition59 : FengMalleProposition59Certificate
      (A := A) (FMWeight := FMWeight)
      fieldAutomorphisms diagonalAutomorphisms isTOne)
    (weight : CorrectedWeight) :
    FixedBy diagonalAutomorphisms weight ↔
      isTOne (correctedWeightLabel fieldAutomorphisms
        diagonalAutomorphisms isTOne WeightAdapter Proposition59 weight) := by
  rw [fixedBy_iff_of_equivariant_equiv diagonalAutomorphisms
    WeightAdapter hWeight weight]
  change FixedBy diagonalAutomorphisms (WeightAdapter weight) ↔ _
  exact Proposition59.diagonal_fixed_iff _

end CorrespondenceTransport

/-! ## The actual Proposition 5.4 local-factor binding -/

section NonXCorrection

variable {FMWeight FMFactor Gamma MultiplicityCentralizer : Type u}
variable [Group MultiplicityCentralizer]

/-- The part of the assignment formula in Feng--Malle, Proposition 5.4,
needed after restricting to its actual principal local-factor carrier. -/
structure FengMalleProposition54AssignmentCertificate
    (D : PrincipalLabelData Gamma)
    (Factors : PrincipalLocalFactorSystem
      FMWeight FMFactor Gamma MultiplicityCentralizer) where
  amount_positive : ∀ factor, 0 < Factors.amount factor
  amount_le_weight : ∀ factor,
    Factors.amount factor ≤ D.weightParameter (Factors.elementaryDivisor factor)

variable {CorrectedWeight CorrectedFactor : Type u}
variable {A G CorrectedLocalCharacter FMLocalCharacter Block : Type u}
variable [Group A] [Group G]
variable [MulAction A CorrectedWeight] [MulAction A FMWeight]
variable (principalBlock : Block)
variable
  (Corrected : PrincipalWeightRealisation
    (G := G) CorrectedWeight CorrectedLocalCharacter principalBlock)
  (FM : PrincipalWeightRealisation
    (G := G) FMWeight FMLocalCharacter principalBlock)
  (CorrectedFactors : PrincipalLocalFactorSystem
    CorrectedWeight CorrectedFactor Gamma MultiplicityCentralizer)
  (FMFactors : PrincipalLocalFactorSystem
    FMWeight FMFactor Gamma MultiplicityCentralizer)
  (Adapter : RestrictedCorrectedPrincipalFibreAdapter
    (A := A) principalBlock Corrected FM CorrectedFactors FMFactors)
  (D : PrincipalLabelData Gamma)
  (Proposition54 : FengMalleProposition54AssignmentCertificate D FMFactors)

include Corrected FM FMFactors Adapter Proposition54

/-- Map an actual corrected non-`x-1` factor to the exact synthetic carrier
whose emptiness was already checked.  The elementary divisor and amount come
from that same factor through the restricted carrier adapter. -/
def correctedFactorToNonXContribution
    (factor : CorrectedFactor)
    (hGamma : CorrectedFactors.elementaryDivisor factor ≠ D.xMinusOne) :
    NonXLocalContribution D where
  gamma := FMFactors.elementaryDivisor (Adapter.factorEquiv factor)
  gamma_ne_xMinusOne := by
    intro h
    apply hGamma
    rw [← Adapter.factor_elementaryDivisor_preserved factor, h]
  amount := FMFactors.amount (Adapter.factorEquiv factor)
  amount_positive := Proposition54.amount_positive _
  amount_le_weight := Proposition54.amount_le_weight _

/-- There is no actual corrected non-`x-1` local factor. -/
theorem correctedNonXLocalFactor_isEmpty :
    IsEmpty { factor : CorrectedFactor //
      CorrectedFactors.elementaryDivisor factor ≠ D.xMinusOne } := by
  constructor
  intro factor
  let contribution : NonXLocalContribution D :=
    correctedFactorToNonXContribution principalBlock Corrected FM
      CorrectedFactors FMFactors Adapter D Proposition54 factor.1 factor.2
  exact @isEmptyElim (NonXLocalContribution D)
    D.nonXLocalContribution_isEmpty (fun _ => False) contribution

end NonXCorrection

/-! ## Surviving `x-1` factors and the unaffected Feng--Malle carrier -/

section SurvivingFactors

variable {CorrectedWeight FMWeight CorrectedFactor FMFactor Gamma : Type u}
variable {MultiplicityCentralizer : Type u} [Group MultiplicityCentralizer]
variable (D : PrincipalLabelData Gamma)
variable
  (CorrectedFactors : PrincipalLocalFactorSystem
    CorrectedWeight CorrectedFactor Gamma MultiplicityCentralizer)
  (FMFactors : PrincipalLocalFactorSystem
    FMWeight FMFactor Gamma MultiplicityCentralizer)

/-- FYZ, Proposition 3.48(3) with Remarks 3.49--3.50, restricted to the
surviving principal `R^0` factors: their multiplicity is one. -/
structure FYZProposition3483MultiplicityOneCertificate where
  multiplicity_one : ∀ factor,
    CorrectedFactors.elementaryDivisor factor = D.xMinusOne →
    CorrectedFactors.IsRZero factor →
    CorrectedFactors.multiplicity factor = 1

/-- The corrected centraliser formula in the proof of FYZ Proposition 3.48,
restricted to multiplicity one: its carrier is `O_1(q) = {I,-I}`. -/
structure FYZProposition348ProofO1CentralizerCertificate where
  centralizer_eq_signs : ∀ factor,
    CorrectedFactors.elementaryDivisor factor = D.xMinusOne →
    CorrectedFactors.IsRZero factor →
    (CorrectedFactors.multiplicityCentralizer factor :
      Set MultiplicityCentralizer) = {1, CorrectedFactors.minusIdentity}

/-- The unaffected source statement from An (4F)(b), as used in
Feng--Malle, Section 5.1, on the *Feng--Malle* local-factor carrier. -/
structure AnFourFbFengMalleSection51Certificate where
  IsDescribedFactor : FMFactor → Prop
  described_of_xMinusOne_rZero : ∀ factor,
    FMFactors.elementaryDivisor factor = D.xMinusOne →
    FMFactors.IsRZero factor → IsDescribedFactor factor

variable {A G CorrectedLocalCharacter FMLocalCharacter Block : Type u}
variable [Group A] [Group G]
variable [MulAction A CorrectedWeight] [MulAction A FMWeight]
variable (principalBlock : Block)
variable
  (Corrected : PrincipalWeightRealisation
    (G := G) CorrectedWeight CorrectedLocalCharacter principalBlock)
  (FM : PrincipalWeightRealisation
    (G := G) FMWeight FMLocalCharacter principalBlock)
  (Adapter : RestrictedCorrectedPrincipalFibreAdapter
    (A := A) principalBlock Corrected FM CorrectedFactors FMFactors)
  (MultiplicityOne : FYZProposition3483MultiplicityOneCertificate
    D CorrectedFactors)
  (O1Centralizer : FYZProposition348ProofO1CentralizerCertificate
    D CorrectedFactors)
  (AnFM : AnFourFbFengMalleSection51Certificate D FMFactors)

include MultiplicityOne O1Centralizer

/-- On the exact FM factor corresponding to a surviving corrected factor,
the FYZ multiplicity/centraliser correction and the unaffected An--FM
description hold simultaneously. -/
theorem survivingFactor_transport_to_FengMalle
    (factor : CorrectedFactor)
    (hGamma : CorrectedFactors.elementaryDivisor factor = D.xMinusOne)
    (hRZero : CorrectedFactors.IsRZero factor) :
    FMFactors.multiplicity (Adapter.factorEquiv factor) = 1 ∧
      (FMFactors.multiplicityCentralizer (Adapter.factorEquiv factor) :
        Set MultiplicityCentralizer) = {1, FMFactors.minusIdentity} ∧
      AnFM.IsDescribedFactor (Adapter.factorEquiv factor) := by
  have hFMGamma :
      FMFactors.elementaryDivisor (Adapter.factorEquiv factor) =
        D.xMinusOne :=
    (Adapter.factor_elementaryDivisor_preserved factor).trans hGamma
  have hFMRZero : FMFactors.IsRZero (Adapter.factorEquiv factor) :=
    (Adapter.factor_rZero_preserved factor).2 hRZero
  refine ⟨?_, ?_, AnFM.described_of_xMinusOne_rZero _ hFMGamma hFMRZero⟩
  · rw [Adapter.factor_multiplicity_preserved]
    exact MultiplicityOne.multiplicity_one factor hGamma hRZero
  · rw [Adapter.factor_centralizer_preserved,
      O1Centralizer.centralizer_eq_signs factor hGamma hRZero,
      Adapter.minusIdentity_preserved]

end SurvivingFactors

/-! ## Explicit FYZ named-class/decomposition binding and K exclusion -/

section FYZOmittedFamily

variable {F : Type u} [Field F] [Finite F]
variable {Rest : Type u} [Fintype Rest] [DecidableEq Rest]

noncomputable local instance sourceWreathPointsFintype (cs : List Nat) :
    Fintype (SourceWreathPoints cs) := Fintype.ofFinite _

noncomputable local instance sourceWreathPointsDecidableEq (cs : List Nat) :
    DecidableEq (SourceWreathPoints cs) := Classical.decEq _

variable {n : Nat} {cs : List Nat} {d : Fin (n + 2) → F}
variable {K : Matrix Rest Rest F}

abbrev FYZAmbient := FormIsometryGroup (correctedFullGram n cs d K)

/-- Interpretation of the two named FYZ source classes.  This contains no
evidence; in particular the `.zero` tag does not prove the first predicate. -/
structure FYZNamedFamilySemantics where
  IsNamedEquation335AlphaZeroRightFactor :
    Subgroup (FormIsometryGroup (omega (F := F))) → Prop
  IsNamedCorrectedEvenFamily : Subgroup (FYZAmbient (n := n) (cs := cs)
    (d := d) (K := K)) → Prop

variable {CorrectedWeight CorrectedLocalCharacter Block : Type u}
variable {Occurrence : Type u}
variable (principalBlock : Block)
variable
  (Corrected : PrincipalWeightRealisation
    (G := FYZAmbient (n := n) (cs := cs) (d := d) (K := K))
    CorrectedWeight CorrectedLocalCharacter principalBlock)
  (Semantics : FYZNamedFamilySemantics
    (F := F) (n := n) (cs := cs) (d := d) (K := K))

/-- Equation (3.35), with the required source identification stated
separately from the `FYZRightFactor .zero` tag. -/
structure FYZEquation335Certificate where
  decomposition : Occurrence → FYZEquation335Decomposition n cs d K
  named_alphaZero_rightFactor : ∀ occurrence : Occurrence,
    Semantics.IsNamedEquation335AlphaZeroRightFactor
      (decomposition occurrence).equation335RightFactor.subgroup

variable (Equation335 : FYZEquation335Certificate
  (Occurrence := Occurrence) Semantics)

/-- FYZ Theorem 3.37: the equation-(3.35) factor and the remaining direct
factors give the named full subgroup, up to the supplied conjugator. -/
structure FYZTheorem337DecompositionCertificate where
  namedCorrectedSubgroup : Occurrence → Subgroup
    (FYZAmbient (n := n) (cs := cs) (d := d) (K := K))
  named_corrected_family : ∀ occurrence : Occurrence,
    Semantics.IsNamedCorrectedEvenFamily
      (namedCorrectedSubgroup occurrence)
  decomposition_eq_named : ∀ occurrence : Occurrence,
    (Equation335.decomposition occurrence).subgroup =
      namedCorrectedSubgroup occurrence

variable (Theorem337 : FYZTheorem337DecompositionCertificate
  (Occurrence := Occurrence) Semantics Equation335)

/-- FYZ Proposition 3.48(4), after Remark 3.36's correction: an actual
occurrence in the corrected set of weights in the principal block has exactly the named
radical subgroup.  No nonoccurrence or principal exclusion is a field. -/
structure FYZProposition3484OccurrenceCertificate where
  weight : Occurrence → CorrectedWeight
  radical_eq_named : ∀ occurrence : Occurrence,
    Corrected.radical (weight occurrence) =
      Theorem337.namedCorrectedSubgroup occurrence

/-- The exact necessary direction of FYZ Lemma 2.3 on the actual principal
set of weights. -/
structure FYZLemma23PrincipalCarrierCertificate where
  centre_is_sylow : ∀ weight : CorrectedWeight,
    ∃ P : Sylow 2
        (Subgroup.centralizer
          (Corrected.radical weight : Set
            (FYZAmbient (n := n) (cs := cs) (d := d) (K := K)))),
      (P : Subgroup
        (Subgroup.centralizer
          (Corrected.radical weight : Set
            (FYZAmbient (n := n) (cs := cs) (d := d) (K := K))))) =
        sourceCentreInCentralizer (Corrected.radical weight)

/-- Every explicitly bound occurrence of the corrected even-multiplicity
family is empty.  This is just the existing K exclusion applied after the
three source carrier equalities above. -/
theorem fyzOmittedEvenOccurrence_isEmpty
    (hTwo : (2 : F) ≠ 0)
    (Proposition348 : FYZProposition3484OccurrenceCertificate
      principalBlock Corrected Semantics Equation335 Theorem337)
    (Lemma23 : FYZLemma23PrincipalCarrierCertificate
      principalBlock Corrected) :
    IsEmpty Occurrence := by
  constructor
  intro occurrence
  let D := Equation335.decomposition occurrence
  have hRadical :
      Corrected.radical (Proposition348.weight occurrence) = D.subgroup :=
    (Proposition348.radical_eq_named occurrence).trans
      (Theorem337.decomposition_eq_named occurrence).symm
  have hClause : FYZPrincipalCentreSylowClause D.subgroup True := by
    intro _
    have hSylow :=
      Lemma23.centre_is_sylow (Proposition348.weight occurrence)
    rw [hRadical] at hSylow
    exact hSylow
  exact (equation335_source_instantiated_principal_exclusion
    hTwo D True hClause) trivial

end FYZOmittedFamily

/-! ## Component-level moving-window output -/

section Window

variable {A G Brauer FMBrauer CorrectedWeight FMWeight : Type u}
variable {CorrectedLocalCharacter FMLocalCharacter Block : Type u}
variable {ULabel TLabel Gamma CorrectedFactor FMFactor : Type u}
variable {MultiplicityCentralizer : Type u}
variable [Group A] [Group G] [Group MultiplicityCentralizer]
variable [MulAction A Brauer] [MulAction A FMBrauer]
variable [MulAction A CorrectedWeight] [MulAction A FMWeight]

/-- The strongest aggregate produced by this file.  It is deliberately a
record of components, not a BAW/iBAW predicate.  The correction exclusions
are separate theorems above because the FYZ ambient model has its own field
and matrix parameters. -/
structure FengMallePrincipalBlockCorrespondence
    (principalBlock : Block)
    (BrauerData : PrincipalBrauerRealisation
      (Brauer := Brauer) principalBlock)
    (CorrectedData : PrincipalWeightRealisation
      (G := G) CorrectedWeight CorrectedLocalCharacter principalBlock)
    (fieldAutomorphisms diagonalAutomorphisms : Subgroup A)
    (isUOne : ULabel → Prop) (isTOne : TLabel → Prop) where
  omega : Brauer ≃ CorrectedWeight
  omega_equivariant : ∀ (a : A) (chi : Brauer),
    omega (a • chi) = a • omega chi
  brauer_block : ∀ chi, BrauerData.blockOf chi = principalBlock
  weight_block : ∀ weight,
    CorrectedData.inducedBlock (CorrectedData.localCharacter weight) =
      principalBlock
  brauerLabel : Brauer ≃ ULabel
  weightLabel : CorrectedWeight ≃ TLabel
  brauer_field_fixed : ∀ chi : Brauer, FixedBy fieldAutomorphisms chi
  weight_field_fixed : ∀ weight : CorrectedWeight,
    FixedBy fieldAutomorphisms weight
  brauer_diagonal_fixed_iff : ∀ chi : Brauer,
    FixedBy diagonalAutomorphisms chi ↔ isUOne (brauerLabel chi)
  weight_diagonal_fixed_iff : ∀ weight : CorrectedWeight,
    FixedBy diagonalAutomorphisms weight ↔ isTOne (weightLabel weight)

variable (principalBlock : Block)
variable
  (BrauerData : PrincipalBrauerRealisation
    (Brauer := Brauer) principalBlock)
  (CorrectedData : PrincipalWeightRealisation
    (G := G) CorrectedWeight CorrectedLocalCharacter principalBlock)
  (FMData : PrincipalWeightRealisation
    (G := G) FMWeight FMLocalCharacter principalBlock)
  (CorrectedFactors : PrincipalLocalFactorSystem
    CorrectedWeight CorrectedFactor Gamma MultiplicityCentralizer)
  (FMFactors : PrincipalLocalFactorSystem
    FMWeight FMFactor Gamma MultiplicityCentralizer)
  (BrauerAdapter : FengMallePrincipalBrauerCarrierAdapter
    (A := A) (Brauer := Brauer) (FMBrauer := FMBrauer))
  (WeightAdapter : RestrictedCorrectedPrincipalFibreAdapter
    (A := A) principalBlock CorrectedData FMData CorrectedFactors FMFactors)
variable (fieldAutomorphisms diagonalAutomorphisms : Subgroup A)
variable (isUOne : ULabel → Prop) (isTOne : TLabel → Prop)
variable
  (Corollary43 : FengMalleCorollary43Certificate
    (A := A) (FMBrauer := FMBrauer)
    fieldAutomorphisms diagonalAutomorphisms isUOne)
  (Proposition59 : FengMalleProposition59Certificate
    (A := A) (FMWeight := FMWeight)
    fieldAutomorphisms diagonalAutomorphisms isTOne)
  (Theorem62 : FengMalleTheorem62Certificate
    (A := A) (FMBrauer := FMBrauer) (FMWeight := FMWeight))

/-- Combine only the concrete principal-fibre correspondence data supplied
by the three exact Feng--Malle source results and the explicit carrier
adapters. -/
def principalBlockCorrespondence :
    FengMallePrincipalBlockCorrespondence principalBlock BrauerData
      CorrectedData fieldAutomorphisms diagonalAutomorphisms isUOne isTOne where
  omega := correctedPrincipalEquiv BrauerAdapter Theorem62
    WeightAdapter.weightEquiv
  omega_equivariant := correctedPrincipalEquiv_equivariant
    BrauerAdapter Theorem62 WeightAdapter.weightEquiv
      WeightAdapter.weightEquivariant
  brauer_block := BrauerData.block_eq_principal
  weight_block := CorrectedData.inducedBlock_eq_principal
  brauerLabel := correctedBrauerLabel fieldAutomorphisms
    diagonalAutomorphisms isUOne BrauerAdapter Corollary43
  weightLabel := correctedWeightLabel fieldAutomorphisms
    diagonalAutomorphisms isTOne WeightAdapter.weightEquiv Proposition59
  brauer_field_fixed := correctedBrauer_field_fixed
    fieldAutomorphisms diagonalAutomorphisms isUOne BrauerAdapter Corollary43
  weight_field_fixed := correctedWeight_field_fixed
    fieldAutomorphisms diagonalAutomorphisms isTOne WeightAdapter.weightEquiv
      WeightAdapter.weightEquivariant Proposition59
  brauer_diagonal_fixed_iff := correctedBrauer_diagonal_fixed_iff
    fieldAutomorphisms diagonalAutomorphisms isUOne BrauerAdapter Corollary43
  weight_diagonal_fixed_iff := correctedWeight_diagonal_fixed_iff
    fieldAutomorphisms diagonalAutomorphisms isTOne WeightAdapter.weightEquiv
      WeightAdapter.weightEquivariant Proposition59

end Window

/-! ## Fixed Definition 3.5 carrier for the symplectic principal block -/

section FixedPrincipalSpCarrier

variable (P : Definition35Problem)
variable {FMBrauer FMWeight ULabel TLabel : Type u}
variable {CorrectedLocalCharacter FMLocalCharacter : Type u}
variable {Gamma CorrectedFactor FMFactor MultiplicityCentralizer : Type u}
variable [Group MultiplicityCentralizer]
variable [MulAction P.Gamma FMBrauer] [MulAction P.Gamma FMWeight]

local instance principalSpBrauerAction :
    MulAction P.Gamma (Definition35Brauer P) :=
  definition35BrauerAction P

local instance principalSpWeightAction :
    MulAction P.Gamma (Definition35Weight P) :=
  definition35WeightAction P

/-- Fixed-carrier output of the Feng--Malle principal-block map.

`P` already contains the literal Brauer fibre, weight fibre, local block
induction, and the action of the proposed block stabiliser.  This structure
adds the transported Theorem 6.2 map and the two exact stabiliser statements;
it deliberately has no modular-character-triple field. -/
structure PrincipalSpMapSource
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (fieldAutomorphisms diagonalAutomorphisms : Subgroup P.Gamma)
    (isUOne : ULabel → Prop) (isTOne : TLabel → Prop) where
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  brauerLabel : Definition35Brauer P ≃ ULabel
  weightLabel : Definition35Weight P ≃ TLabel
  brauer_field_fixed : ∀ chi : Definition35Brauer P,
    FixedBy fieldAutomorphisms chi
  weight_field_fixed : ∀ weight : Definition35Weight P,
    FixedBy fieldAutomorphisms weight
  brauer_diagonal_fixed_iff : ∀ chi : Definition35Brauer P,
    FixedBy diagonalAutomorphisms chi ↔ isUOne (brauerLabel chi)
  weight_diagonal_fixed_iff : ∀ weight : Definition35Weight P,
    FixedBy diagonalAutomorphisms weight ↔ isTOne (weightLabel weight)

variable
  (CorrectedData : PrincipalWeightRealisation
    (G := P.H) (Definition35Weight P) CorrectedLocalCharacter P.block)
  (FMData : PrincipalWeightRealisation
    (G := P.H) FMWeight FMLocalCharacter P.block)
  (CorrectedFactors : PrincipalLocalFactorSystem
    (Definition35Weight P) CorrectedFactor Gamma MultiplicityCentralizer)
  (FMFactors : PrincipalLocalFactorSystem
    FMWeight FMFactor Gamma MultiplicityCentralizer)
  (BrauerAdapter : FengMallePrincipalBrauerCarrierAdapter
    (A := P.Gamma) (Brauer := Definition35Brauer P)
      (FMBrauer := FMBrauer))
  (WeightAdapter : RestrictedCorrectedPrincipalFibreAdapter
    (A := P.Gamma) P.block CorrectedData FMData
      CorrectedFactors FMFactors)
variable (automorphisms : Definition35AutomorphismStabilizerAdapter P)
variable (fieldAutomorphisms diagonalAutomorphisms : Subgroup P.Gamma)
variable (isUOne : ULabel → Prop) (isTOne : TLabel → Prop)
variable
  (Corollary43 : FengMalleCorollary43Certificate
    (A := P.Gamma) (FMBrauer := FMBrauer)
      fieldAutomorphisms diagonalAutomorphisms isUOne)
  (Proposition59 : FengMalleProposition59Certificate
    (A := P.Gamma) (FMWeight := FMWeight)
      fieldAutomorphisms diagonalAutomorphisms isTOne)
  (Theorem62 : FengMalleTheorem62Certificate
    (A := P.Gamma) (FMBrauer := FMBrauer) (FMWeight := FMWeight))

/-- Transport the three Feng--Malle results to the characters and weights of
the fixed principal block in Definition 3.5. The identification of the
corrected principal weight fibre remains an explicit hypothesis. -/
def principalSpMapSource :
    PrincipalSpMapSource P automorphisms fieldAutomorphisms
      diagonalAutomorphisms isUOne isTOne where
  omega := correctedPrincipalEquiv BrauerAdapter Theorem62
    WeightAdapter.weightEquiv
  equivariant := by
    simpa only [Definition35Equivariant] using
      (correctedPrincipalEquiv_equivariant BrauerAdapter Theorem62
        WeightAdapter.weightEquiv WeightAdapter.weightEquivariant)
  brauerLabel := correctedBrauerLabel fieldAutomorphisms
    diagonalAutomorphisms isUOne BrauerAdapter Corollary43
  weightLabel := correctedWeightLabel fieldAutomorphisms
    diagonalAutomorphisms isTOne WeightAdapter.weightEquiv Proposition59
  brauer_field_fixed := correctedBrauer_field_fixed fieldAutomorphisms
    diagonalAutomorphisms isUOne BrauerAdapter Corollary43
  weight_field_fixed := correctedWeight_field_fixed fieldAutomorphisms
    diagonalAutomorphisms isTOne WeightAdapter.weightEquiv
      WeightAdapter.weightEquivariant Proposition59
  brauer_diagonal_fixed_iff := correctedBrauer_diagonal_fixed_iff
    fieldAutomorphisms diagonalAutomorphisms isUOne BrauerAdapter Corollary43
  weight_diagonal_fixed_iff := correctedWeight_diagonal_fixed_iff
    fieldAutomorphisms diagonalAutomorphisms isTOne WeightAdapter.weightEquiv
      WeightAdapter.weightEquivariant Proposition59

/-! The modular-character-triple relation is intentionally not credited to
Corollary 4.3, Proposition 5.9, or Theorem 6.2. -/

/-- The exact pointwise U/E2 relation still required by Feng--Li--Zhang,
Definition 3.5(ii), on the same map and same fixed carriers.  This is not a
free `CharacterTripleOK` predicate: `source` fixes the project-wide semantic
relation and `Map.omega` fixes both arguments. -/
structure PrincipalSpDefinition35LocalSource
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (source : FLZSourceSemantics P automorphisms)
    {fieldAutomorphisms diagonalAutomorphisms : Subgroup P.Gamma}
    {isUOne : ULabel → Prop} {isTOne : TLabel → Prop}
    (Map : PrincipalSpMapSource P automorphisms fieldAutomorphisms
      diagonalAutomorphisms isUOne isTOne) where
  blockIsomorphism_at : ∀ psi : Definition35Brauer P,
    source.definition35BlockIsomorphic psi (Map.omega psi)

/-- Kernel packaging into the existing fixed Definition 3.5 carrier.  This
does not assert BAW-goodness, all-block iBAW, or the manuscript proposition. -/
def PrincipalSpMapSource.toDefinition35IBAWBijection
    {automorphisms : Definition35AutomorphismStabilizerAdapter P}
    {source : FLZSourceSemantics P automorphisms}
    {fieldAutomorphisms diagonalAutomorphisms : Subgroup P.Gamma}
    {isUOne : ULabel → Prop} {isTOne : TLabel → Prop}
    (Map : PrincipalSpMapSource P automorphisms fieldAutomorphisms
      diagonalAutomorphisms isUOne isTOne)
    (Local : PrincipalSpDefinition35LocalSource P automorphisms source Map) :
    Definition35IBAWBijection P automorphisms source where
  omega := Map.omega
  equivariant := Map.equivariant
  blockIsomorphism := Local.blockIsomorphism_at

end FixedPrincipalSpCarrier

end ModularRep.PaperProofs.OddTwoPrincipalBlockMovingWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
