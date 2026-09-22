import ManuscriptIBAW.Sporadic.Fi24Three
import ManuscriptIBAW.Sporadic.Fi24Five
import ManuscriptIBAW.Sporadic.Fi24Seven
import ManuscriptIBAW.Sporadic.Fi24Cyclic

/-!
Logical axiom dependencies for the Fischer arguments. They do not discharge
the explicit published, table, root or named group interpretations.
-/

#print axioms ManuscriptIBAW.Sporadic.Fi24ThreeLocal.intervalSource
#print axioms ManuscriptIBAW.Sporadic.Fi24ThreeLocal.intervalEvaluation_one
#print axioms ManuscriptIBAW.Sporadic.Fi24ThreeLocal.row_block
#print axioms ManuscriptIBAW.Sporadic.Fi24ThreeLocal.radical_support
#print axioms ManuscriptIBAW.Sporadic.Fi24Three.SourceInputs.complete
#print axioms ManuscriptIBAW.Sporadic.Fi24Three.Inputs.complete
#print axioms ManuscriptIBAW.Sporadic.Fi24Five.Inputs.model
#print axioms ManuscriptIBAW.Sporadic.Fi24Five.SourceInputs.model_eq_retained
#print axioms ManuscriptIBAW.Sporadic.Fi24Five.Inputs.complete
#print axioms ManuscriptIBAW.Sporadic.Fi24Seven.Inputs.model
#print axioms ManuscriptIBAW.Sporadic.Fi24Seven.SourceInputs.model_eq_retained
#print axioms ManuscriptIBAW.Sporadic.Fi24Seven.Inputs.complete
#print axioms ManuscriptIBAW.Sporadic.Fi24Cyclic.Inputs.model
#print axioms ManuscriptIBAW.Sporadic.Fi24Cyclic.SourceInputs.model_eq_retained
#print axioms ManuscriptIBAW.Sporadic.Fi24Cyclic.Inputs.complete
#print axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3Rows.literalV3Binding
#print axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalProbeAction.local_fixed_card_two
#print axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature.actual_b1_card_four
#print axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature.actual_b1_fixed_card_two
#print axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins.actual_counts_of_five_literal_rows
#print axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins.actual_counts_of_seven_sector_cancellation
#print axioms ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins.actual_counts_of_cyclic_blocks

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/

