import ModularRep.AxiomGate
import ModularRep.Manuscript

-- These commands inspect the declarations; they do not instantiate external inputs.
assert_only_standard_axioms ModularRep.LinearBlockStabilizer.ordinary_block_stabilizer_bound
assert_no_direct_conclusion_hypothesis ModularRep.LinearBlockStabilizer.ordinary_block_stabilizer_bound
assert_only_standard_axioms ModularRep.LinearBlockStabilizer.brauer_quotient_block_stabilizer_bound
assert_no_direct_conclusion_hypothesis ModularRep.LinearBlockStabilizer.brauer_quotient_block_stabilizer_bound
assert_only_standard_axioms ModularRep.CurrentSpathCriterion.current_theorem_2_3
assert_no_direct_conclusion_hypothesis ModularRep.CurrentSpathCriterion.current_theorem_2_3
assert_only_standard_axioms ModularRep.CurrentSpathDescent.current_corollary_2_5
assert_no_direct_conclusion_hypothesis ModularRep.CurrentSpathDescent.current_corollary_2_5
assert_only_standard_axioms ModularRep.PaperProofs.CurrentCentralQuotientBijection.lemma_2_6_compatibleBijection
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.CurrentCentralQuotientBijection.lemma_2_6_compatibleBijection
assert_only_standard_axioms ModularRep.PaperProofs.CurrentCyclicOuterBAW.lemma_2_10_bawGood
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.CurrentCyclicOuterBAW.lemma_2_10_bawGood
assert_only_standard_axioms ModularRep.PaperProofs.CurrentFiniteSplittingAssembly.fullFamily
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.CurrentFiniteSplittingAssembly.fullFamily
assert_only_standard_axioms ModularRep.PaperProofs.TypeCCurrentAllCaseSourceApplication.full_block_condition_source_instantiated
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeCCurrentAllCaseSourceApplication.full_block_condition_source_instantiated
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentCliffordStabilizer.lemma46
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentCliffordStabilizer.lemma46
assert_only_standard_axioms ModularRep.PaperProofs.TypeAQuasisimpleSource.ApplicationData.hasDefinition35IBAWFamilyWitness
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeAQuasisimpleSource.ApplicationData.hasDefinition35IBAWFamilyWitness
assert_only_standard_axioms ModularRep.PaperProofs.TypeAQuasisimpleSource.ApplicationData.blockWitness
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeAQuasisimpleSource.ApplicationData.blockWitness
assert_only_standard_axioms ModularRep.PaperProofs.EvenFieldProposition39TypeA.FLZ2023TypeACompositeSource.toCoverFree
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.EvenFieldProposition39TypeA.FLZ2023TypeACompositeSource.toCoverFree
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.principal_series_eq
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.principal_series_eq
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.quasiIsolated_character_principal
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.quasiIsolated_character_principal
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.strictlyQuasiIsolated_iff_principal
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.strictlyQuasiIsolated_iff_principal
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.lemma_4_8
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.lemma_4_8
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.toLegacyCertificate
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentPrincipalSeries.toLegacyCertificate
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis.proposition_4_12
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis.proposition_4_12
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentCompletion.primeTwo
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentCompletion.primeTwo
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentCompletion.complete
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentCompletion.complete
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentCompletion.allPrimes
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentCompletion.allPrimes
assert_only_standard_axioms ModularRep.PaperProofs.TypeBCurrentTheorem.finite_simple_typeB
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.TypeBCurrentTheorem.finite_simple_typeB
assert_only_standard_axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.sporadic_from_external_inputs
assert_no_direct_conclusion_hypothesis ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.sporadic_from_external_inputs
-- This library audit does not import the application. The assertions for
-- theorem_1_1 and corollary_1_2 belong to ManuscriptIBAW.MainAudit and must
-- be run separately. Merely elaborating this file does not check them.

open scoped MonoidAlgebra

namespace TypeBPrincipalSeriesRankTwoAudit

open ModularRep ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.TypeBCliffordCarriers
open ModularRep.PaperProofs.TypeBConformalDualCarriers
open ModularRep.PaperProofs.TypeBCentralKernelBlockSource
open ModularRep.PaperProofs.TypeBCurrentPrincipalSeries

variable {r f : ℕ} {F k K O : Type}
  [Field F] [Finite F] [CharP F r]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [CommRing O] [IsDomain O] [Algebra O K]
  {N : NormSource 2 F} [Finite (Spin 2 F N)]
  (parameters : OddFieldParameters F r f)
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 2 F N))
  [Fintype (LiteralPrimitiveBlock k (Spin 2 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin 2 F N) => b.val))
  (C : Context Msys iota blocks parameters (show 2 ≤ 2 from le_rfl))
  (ce : CE2114Source C)
  (D : DualGeometry parameters (show 2 ≤ 2 from le_rfl))
  (bonnafe : BonnafeSource D)
  (labels : BlockLabelSource C)

include ce bonnafe in
/-- The complete three-clause endpoint specializes to rank two without
an inhabitant, a rank-three hypothesis, or any legacy certificate. -/
theorem rank_two_all_clauses :
    ({chi : Irr K (Spin 2 F N) | C.ordinary.ordinaryBlock chi = C.principalBlock} =
      {chi : Irr K (Spin 2 F N) | IdentityTwoSeries C.rationalSeries chi}) ∧
    (∀ (s : PCSp F 2) (chi : Irr K (Spin 2 F N)),
      D.QuasiIsolated s → C.rationalSeries s chi →
        C.ordinary.ordinaryBlock chi = C.principalBlock) ∧
    (∀ b : LiteralPrimitiveBlock k (Spin 2 F N),
      StrictlyQuasiIsolatedBlock C D labels b ↔ IsPrincipal b) :=
  lemma_4_8 C ce D bonnafe labels

assert_only_standard_axioms rank_two_all_clauses
assert_no_direct_conclusion_hypothesis rank_two_all_clauses

end TypeBPrincipalSeriesRankTwoAudit


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
