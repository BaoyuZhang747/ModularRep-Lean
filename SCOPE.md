# Mathematical scope

This release is a checked Lean companion under its stated external assumptions.
The application endpoints are `ManuscriptIBAW.Main.theorem_1_1` and
`ManuscriptIBAW.Main.corollary_1_2`. The formalisation report identifies the
deductions, their Lean declarations and the assumptions supplied to them.

The triple cover application assumes compatible extension and intermediate
block witnesses for the selected correspondence. The Type C principal
field invariance and counts, central descent, coefficient conventions and
group and character interpretations have their stated external hypotheses.
Neither complete collection of classical and sporadic source assumptions has
been constructed in this companion, and their joint satisfiability has not been
established. These are explicit inputs to the conditional results.

The recorded compilation and audits check deductions from those inputs.
Compilation does not establish the external assumptions. The axiom checks allow
only `propext`, `Classical.choice` and `Quot.sound`. The direct conclusion
check detects a leading hypothesis definitionally equal to the conclusion.
It does not detect logical equivalence, conclusions within structure fields
or circular dependence among several hypotheses. The verification records
describe the commands, checked source identities and scope of each check.

Report Appendix C, "Further constructions in the source library", describes
auxiliary source constructions. The modules
`TypeBRankThreeProductRawWeightBlock`, `TypeBRankThreeMoritaSelectedApplication`
and `TypeBRankThreeSameFieldAutomorphism` have no consumers in the shipped Lean
import/use graph. Their statements therefore concern the auxiliary library,
without asserting their integration into the application endpoints. The report
also makes no claim that its final primitive-block equality is used in the
selected Jordan construction. None of these auxiliary descriptions enlarges
the scope of the recorded Lean checks or discharges the external assumptions.
