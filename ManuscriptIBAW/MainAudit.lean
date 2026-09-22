import ModularRep.AxiomGate
import ManuscriptIBAW.Main

/- These assertions check kernel axiom dependencies and reject a hypothesis
definitionally equal to the endpoint's conclusion. They do not establish
that the source assumptions are inhabited or mathematically sufficient. -/
assert_only_standard_axioms ManuscriptIBAW.Main.theorem_1_1
assert_no_direct_conclusion_hypothesis ManuscriptIBAW.Main.theorem_1_1
assert_only_standard_axioms ManuscriptIBAW.Main.corollary_1_2
assert_no_direct_conclusion_hypothesis ManuscriptIBAW.Main.corollary_1_2
assert_only_standard_axioms ManuscriptIBAW.Main.typeC_complete
assert_no_direct_conclusion_hypothesis ManuscriptIBAW.Main.typeC_complete
assert_only_standard_axioms ManuscriptIBAW.Main.typeB_complete
assert_no_direct_conclusion_hypothesis ManuscriptIBAW.Main.typeB_complete
assert_only_standard_axioms ManuscriptIBAW.Main.sporadic_complete
assert_no_direct_conclusion_hypothesis ManuscriptIBAW.Main.sporadic_complete

#print axioms ManuscriptIBAW.Main.of_allPrimeFamily
#print axioms ManuscriptIBAW.Main.typeC_complete
#print axioms ManuscriptIBAW.Main.typeB_complete
#print axioms ManuscriptIBAW.Main.sporadic_complete
#print axioms ManuscriptIBAW.Main.theorem_1_1
#print axioms ManuscriptIBAW.Main.corollary_1_2
#print ManuscriptIBAW.Main.ClassicalInputs
#print ManuscriptIBAW.FamilyCertificate
#print ManuscriptIBAW.Main.MainCertificate
#print ManuscriptIBAW.Main.SectionEvidence
#print ManuscriptIBAW.Main.FiniteGroupReductionSource
#print axioms ManuscriptIBAW.FamilyCertificate.toLegacy
#print axioms ManuscriptIBAW.Main.FiniteGroupReductionSource.ofLegacy

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The queries inspect the declarations of the accompanying conditional proof.
-/
