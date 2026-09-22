import ManuscriptIBAW.Sporadic.NumericalWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalCompleteCollapse
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-!
# Lemma 5.2 on the specified cover

The premise is numerical equality in every block. The proof chooses
compatible block bijections with the required normalisation for defect zero
characters, proves equivariance because every automorphism is inner, and
constructs extension and block witnesses using local reduction and quotient
block laws. Root agreement is required for those specific witnesses before
the full condition is concluded. The cover is preserved even when its centre is nontrivial.

The sources supply neither a character–weight correspondence nor a complete
inductive condition. The quotient data specify finite complete block decompositions
and the statements used from Navarro–Tiep and Navarro. The ordinary field
has characteristic zero. Algebraic closure is imposed only on the modular
field, and no modular system is required here.
-/

noncomputable section

namespace ManuscriptIBAW.Sporadic.CompleteCollapse

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate

universe u

variable {base : NamedBase.{u}} {p : ℕ} (M : CaseModel base p)

local instance collapseBrauerFintype : Fintype (IBr M.iota) := Fintype.ofFinite _

local notation "inj" =>
  FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding M.iota

/-- Standard local and quotient sources, indexed by the target chosen first. -/
structure Sources where
  localReduction : ∀ W : CharacterWeight p M.K M.X, CanonicalRawReduction M.iota W
  defectZero : DefectZeroReductionSource M.iota
  trivialWeight : TrivialWeightSource (p := p) (X := M.X)
  compatibility : CanonicalLocalBlockCompatibility M.iota M.R.1.operations
  lower : QuotientDataFamily M.iota inj M.R localReduction M.Cover
  coefficient : SpathCoefficientField p M.k M.iota.prime

variable [Fintype (WeightClass (p := p) (K := M.K) (X := M.X))]

/-- Equality in every specified primitive block of the fixed model. -/
def NumericalHypothesis : Prop :=
  letI := M.R.1.operations.ambientBlockData.fintypeBlock
  NumericalBlockwiseAWC (iota := M.iota) (hinj := inj)
    (blocks := M.R.1.operations.ambientBlockData.blocks) (R := M.R)

/-- Lemma 5.2, including covers with nontrivial centre. -/
theorem lemma_5_2 (source : Sources M)
    (allInner : AllAutomorphismsInner (X := M.X))
    (counts : NumericalHypothesis M)
    (roots : OriginalWitnessRoots M.iota M.R M.Cover source.localReduction
      source.defectZero source.trivialWeight (ManuscriptIBAW.Sporadic.OriginalNumericalWitness.witnessOfNumerical
      M.iota inj M.R source.localReduction M.Cover allInner source.defectZero
      source.trivialWeight counts source.compatibility source.lower source.coefficient)) : CaseConclusion M := by
  exact of_original M.iota M.R M.Cover source.localReduction source.defectZero
    source.trivialWeight (ManuscriptIBAW.Sporadic.OriginalNumericalWitness.witnessOfNumerical
      M.iota inj M.R source.localReduction M.Cover allInner source.defectZero
      source.trivialWeight counts source.compatibility source.lower source.coefficient) roots

export ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse
  (exists_definition41_of_numerical)

end ManuscriptIBAW.Sporadic.CompleteCollapse

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
