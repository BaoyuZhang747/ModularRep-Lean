import ManuscriptIBAW.TypeC.LowRankApplications

/-! Logical axiom dependencies and source assumptions for the applications in
small rank. -/

#print axioms ManuscriptIBAW.TypeC.RankTwoCase
#print axioms ManuscriptIBAW.TypeC.rankTwoCase
#print axioms ManuscriptIBAW.TypeC.RankTwoSourceInputs
#print axioms ManuscriptIBAW.TypeC.rankTwoTarget
#print axioms ManuscriptIBAW.TypeC.rankTwo_complete_at_case
#print axioms ManuscriptIBAW.TypeC.Prop34SourceInputs
#print axioms ManuscriptIBAW.TypeC.prop34Target
#print axioms ManuscriptIBAW.TypeC.prop34_full_block_condition
#print axioms ManuscriptIBAW.TypeC.prop34FamilyWitness
#print axioms ManuscriptIBAW.TypeC.lowRankEven_all_odd_primes
#print axioms ManuscriptIBAW.TypeC.Sp6TwoOddInputs
#print axioms ManuscriptIBAW.TypeC.Sp6TwoOddInputs.target
#print axioms ManuscriptIBAW.TypeC.Sp6TwoOddInputs.complete
#print axioms ManuscriptIBAW.TypeC.Sp6TwoOddInputs.projection_eq
#print axioms ManuscriptIBAW.TypeC.sp6Two_all_odd_primes

#print ManuscriptIBAW.TypeC.RankTwoCase
#print ManuscriptIBAW.TypeC.RankTwoSourceInputs
#print ManuscriptIBAW.TypeC.Prop34SourceInputs
#print ManuscriptIBAW.TypeC.Sp6TwoOddInputs
#print ManuscriptIBAW.TypeC.Sp6TwoOddInputs.complete
#check @ManuscriptIBAW.TypeC.prop34_full_block_condition
#check @ManuscriptIBAW.TypeC.sp6Two_all_odd_primes

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
