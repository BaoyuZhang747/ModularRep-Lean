import ManuscriptIBAW.Sporadic.NumericalWitnesses
import ManuscriptIBAW.Sporadic.MonsterNumerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd

/-!
# The Monster applications in Proposition 5.4

The group, root correspondence, primitive block operations and universal
prime-to-p cover determine the model before its conclusion is proved. At
two, numerical subtraction supplies the block counts for Lemma 5.2. At odd
primes, the proof uses the published cyclic and noncyclic counts on the same
cover.

The published numerical results and the interpretations of the named groups,
tables and local characters remain explicit assumptions. Root compatibility is an additional hypothesis on the explicitly constructed
extension and block witnesses. The inputs supply no final correspondence. The ordinary
coefficient field is not required to be the fraction field of a modular
system.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual (WeightClass)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoFullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

universe u

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphisms

namespace ManuscriptIBAW.Sporadic.MonsterTwo

/-- Numerical and structural sources, before requiring common roots. -/
abbrev SourceInputs (base : NamedBase.{u}) := ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.Inputs base

def sourceModel {base : NamedBase.{u}} (inputs : SourceInputs base) :
    CaseModel base 2 := by
  cases inputs with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R source small C cover hcover hkernel hsimple hnonabelian hOuter D T compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource 2 X := identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian
      exact {
        k := k
        K := K
        X := X
        iota := iota
        R := R
        Cover := selectedCover
        baseEquiv := namedBaseEquiv }

/-- Root agreement for the actual witnesses constructed from these inputs. -/
def RootAgreement {base : NamedBase.{u}} (inputs : SourceInputs base) : Prop := by
  cases inputs with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R source small C cover hcover hkernel hsimple hnonabelian hOuter D T compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource 2 X := identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian
      let := source.weight_finite iota hinj R
      let : Fintype (WeightClass (p := 2) (K := K) (X := X)) := Fintype.ofFinite _
      let W := ManuscriptIBAW.Sporadic.CanonicalNumericalWitness.witnessOfNumerical
        iota hinj R C selectedCover (center_eq_bot_of_nonabelian_simple hsimple hnonabelian) (allAutomorphismsInner_of_outer_card_one hOuter) D T
        (ManuscriptIBAW.Sporadic.MonsterNumerical.numericalBlockwiseAWC iota hinj R source small) compatibility fieldSource
      exact CanonicalWitnessRoots iota R selectedCover C D T W

/-- The source data and the root agreement for their constructed witnesses. -/
structure Inputs (base : NamedBase.{u}) where
  source : SourceInputs base
  roots : RootAgreement source

def model {base : NamedBase.{u}} (inputs : Inputs base) : CaseModel base 2 :=
  sourceModel inputs.source

theorem model_eq_retained {base : NamedBase.{u}} (inputs : Inputs base) :
    model inputs = ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.model inputs.source := by
  rcases inputs with ⟨source, roots⟩
  cases source
  rfl

def target {base : NamedBase.{u}} (inputs : Inputs base) : Prop := CaseConclusion (model inputs)

/-- The complete condition uses the same constructed matching and compatible roots. -/
theorem complete {base : NamedBase.{u}} (inputs : Inputs base) : target inputs := by
  rcases inputs with ⟨inputs, roots⟩
  cases inputs with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R source small C cover hcover hkernel hsimple hnonabelian hOuter D T compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource 2 X := identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian
      change Definition41Certificate iota R selectedCover
      let := source.weight_finite iota hinj R
      let : Fintype (WeightClass (p := 2) (K := K) (X := X)) := Fintype.ofFinite _
      let W := ManuscriptIBAW.Sporadic.CanonicalNumericalWitness.witnessOfNumerical
        iota hinj R C selectedCover (center_eq_bot_of_nonabelian_simple hsimple hnonabelian) (allAutomorphismsInner_of_outer_card_one hOuter) D T
        (ManuscriptIBAW.Sporadic.MonsterNumerical.numericalBlockwiseAWC iota hinj R source small) compatibility fieldSource
      exact of_canonical iota R selectedCover C D T (center_eq_bot_of_nonabelian_simple hsimple hnonabelian) W roots

/-- The covering projection lands in the original named simple group. -/
def projection {base : NamedBase.{u}} (inputs : Inputs base) :
    (model inputs).X →* base.S :=
  (model inputs).baseEquiv.toMonoidHom.comp (model inputs).Cover.quotient

theorem projection_surjective {base : NamedBase.{u}} (inputs : Inputs base) :
    Function.Surjective (projection inputs) :=
  (model inputs).baseEquiv.surjective.comp (model inputs).Cover.quotient_surjective

/-- The universal prime-to-p cover in this branch is the simple group itself. -/
theorem cover_bijective {base : NamedBase.{u}} (inputs : Inputs base) :
    Function.Bijective (model inputs).Cover.quotient := by
  rcases inputs with ⟨source, roots⟩
  cases source
  exact Function.bijective_id

/-- The model is returned together with its proved conclusion. -/
def realise {base : NamedBase.{u}} (inputs : Inputs base) :
    {M : CaseModel base 2 // CaseConclusion M} :=
  ⟨model inputs, complete inputs⟩

end ManuscriptIBAW.Sporadic.MonsterTwo

namespace ManuscriptIBAW.Sporadic.MonsterOdd

/-- Numerical and structural sources, before requiring common roots. -/
abbrev SourceInputs (base : NamedBase.{u}) (p : ℕ) := ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.Inputs base p

def sourceModel {base : NamedBase.{u}} {p : ℕ} (inputs : SourceInputs base p) :
    CaseModel base p := by
  cases inputs with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C cover hcover hkernel hsimple hnonabelian hOuter D T hpOdd source compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource p X := identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian
      exact {
        k := k
        K := K
        X := X
        iota := iota
        R := R
        Cover := selectedCover
        baseEquiv := namedBaseEquiv }

/-- Root agreement for the actual witnesses constructed from these inputs. -/
def RootAgreement {base : NamedBase.{u}} {p : ℕ} (inputs : SourceInputs base p) : Prop := by
  cases inputs with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C cover hcover hkernel hsimple hnonabelian hOuter D T hpOdd source compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource p X := identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian
      let W := ManuscriptIBAW.Sporadic.CanonicalNumericalWitness.witnessOfNumerical
        iota hinj R C selectedCover (center_eq_bot_of_nonabelian_simple hsimple hnonabelian) (allAutomorphismsInner_of_outer_card_one hOuter) D T
        (ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical.numericalBlockwiseAWC iota hinj R (source.toDefectCounts iota hinj R hpOdd)) compatibility fieldSource
      exact CanonicalWitnessRoots iota R selectedCover C D T W

/-- The source data and the root agreement for their constructed witnesses. -/
structure Inputs (base : NamedBase.{u}) (p : ℕ) where
  source : SourceInputs base p
  roots : RootAgreement source

def model {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) : CaseModel base p :=
  sourceModel inputs.source

theorem model_eq_retained {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) :
    model inputs = ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.model inputs.source := by
  rcases inputs with ⟨source, roots⟩
  cases source
  rfl

def target {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) : Prop := CaseConclusion (model inputs)

/-- The complete condition uses the same constructed matching and compatible roots. -/
theorem complete {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) : target inputs := by
  rcases inputs with ⟨inputs, roots⟩
  cases inputs with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C cover hcover hkernel hsimple hnonabelian hOuter D T hpOdd source compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource p X := identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian
      change Definition41Certificate iota R selectedCover
      let W := ManuscriptIBAW.Sporadic.CanonicalNumericalWitness.witnessOfNumerical
        iota hinj R C selectedCover (center_eq_bot_of_nonabelian_simple hsimple hnonabelian) (allAutomorphismsInner_of_outer_card_one hOuter) D T
        (ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical.numericalBlockwiseAWC iota hinj R (source.toDefectCounts iota hinj R hpOdd)) compatibility fieldSource
      exact of_canonical iota R selectedCover C D T (center_eq_bot_of_nonabelian_simple hsimple hnonabelian) W roots

/-- The covering projection lands in the original named simple group. -/
def projection {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) :
    (model inputs).X →* base.S :=
  (model inputs).baseEquiv.toMonoidHom.comp (model inputs).Cover.quotient

theorem projection_surjective {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) :
    Function.Surjective (projection inputs) :=
  (model inputs).baseEquiv.surjective.comp (model inputs).Cover.quotient_surjective

/-- The universal prime-to-p cover in this branch is the simple group itself. -/
theorem cover_bijective {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) :
    Function.Bijective (model inputs).Cover.quotient := by
  rcases inputs with ⟨source, roots⟩
  cases source
  exact Function.bijective_id

/-- The model is returned together with its proved conclusion. -/
def realise {base : NamedBase.{u}} {p : ℕ} (inputs : Inputs base p) :
    {M : CaseModel base p // CaseConclusion M} :=
  ⟨model inputs, complete inputs⟩

end ManuscriptIBAW.Sporadic.MonsterOdd

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
