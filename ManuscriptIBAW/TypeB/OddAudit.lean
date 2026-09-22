import ManuscriptIBAW.TypeB.OddInputs

/-!
# Axiom inspection for Type B at odd primes

These queries display the stated conclusions and their Lean axiom
dependencies. The published source assumptions remain explicit arguments.
The queries do not certify their mathematical interpretation or prove that
they can be satisfied.
-/

#check ManuscriptIBAW.TypeB.OddTensorBound.physicalTensorSource
#check ManuscriptIBAW.TypeB.OddTensorBound.norm_center_image
#check ManuscriptIBAW.TypeB.OddTensorBound.index_eq_two
#check ManuscriptIBAW.TypeB.OddTensorBound.stabilizer_structure
#check ManuscriptIBAW.TypeB.OddConlon.decompositionWitness
#check ManuscriptIBAW.TypeB.OddConlon.block_bijection
#check ManuscriptIBAW.TypeB.OddApplication.correspondence
#check ManuscriptIBAW.TypeB.OddApplication.hypotheses
#check ManuscriptIBAW.TypeB.OddApplication.witness
#check ManuscriptIBAW.TypeB.OddUniform.target
#check ManuscriptIBAW.TypeB.OddUniform.complete
#check ManuscriptIBAW.TypeB.OddInputs.Inputs.complete

#print axioms ManuscriptIBAW.TypeB.OddTensorBound.physicalTensorSource
#print axioms ManuscriptIBAW.TypeB.OddTensorBound.index_eq_two
#print axioms ManuscriptIBAW.TypeB.OddTensorBound.stabilizer_structure
#print axioms ManuscriptIBAW.TypeB.OddConlon.decompositionWitness
#print axioms ManuscriptIBAW.TypeB.OddConlon.block_bijection
#print axioms ManuscriptIBAW.TypeB.OddApplication.correspondence
#print axioms ManuscriptIBAW.TypeB.OddApplication.hypotheses
#print axioms ManuscriptIBAW.TypeB.OddApplication.witness
#print axioms ManuscriptIBAW.TypeB.OddUniform.target
#print axioms ManuscriptIBAW.TypeB.OddUniform.complete
#print axioms ManuscriptIBAW.TypeB.OddInputs.Inputs.complete

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
