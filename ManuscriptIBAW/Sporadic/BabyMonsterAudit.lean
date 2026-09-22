import ManuscriptIBAW.Sporadic.BabyApplication
import ManuscriptIBAW.Sporadic.MonsterApplication

/-! Focused kernel queries for the Baby Monster and Monster deductions.
These reports do not discharge the explicit published or structural assumptions. -/

#print axioms ManuscriptIBAW.Sporadic.BabyNumerical.nonprincipal_count
#print axioms ManuscriptIBAW.Sporadic.BabyNumerical.principal_count
#print axioms ManuscriptIBAW.Sporadic.BabyNumerical.all_block_counts
#print axioms ManuscriptIBAW.Sporadic.BabyNumerical.numericalBlockwiseAWC
#print axioms ManuscriptIBAW.Sporadic.BabyNumerical.seven_transcript_values
#print axioms ManuscriptIBAW.Sporadic.MonsterNumerical.nonprincipal_count_eq
#print axioms ManuscriptIBAW.Sporadic.MonsterNumerical.principal_count_eq
#print axioms ManuscriptIBAW.Sporadic.MonsterNumerical.all_block_counts
#print axioms ManuscriptIBAW.Sporadic.MonsterNumerical.numericalBlockwiseAWC
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.model
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.model_eq_retained
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.target
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.complete
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.projection
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.projection_surjective
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.cover_bijective
#print axioms ManuscriptIBAW.Sporadic.BabyTwo.realise
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.model
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.model_eq_retained
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.target
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.complete
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.projection
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.projection_surjective
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.cover_kernel_card
#print axioms ManuscriptIBAW.Sporadic.BabyOdd.realise
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.model
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.model_eq_retained
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.target
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.complete
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.projection
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.projection_surjective
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.cover_bijective
#print axioms ManuscriptIBAW.Sporadic.MonsterTwo.realise
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.model
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.model_eq_retained
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.target
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.complete
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.projection
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.projection_surjective
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.cover_bijective
#print axioms ManuscriptIBAW.Sporadic.MonsterOdd.realise

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
