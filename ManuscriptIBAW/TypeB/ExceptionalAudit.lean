import ManuscriptIBAW.TypeB.ExceptionalPrincipalDescent

/-!
Axiom inspection for Proposition 4.11, its exact cover and the central
descent used for its principal block.
-/

#print axioms ManuscriptIBAW.TypeB.Exceptional.Target.cover
#print axioms ManuscriptIBAW.TypeB.Exceptional.Target.cover_kernel_card
#print axioms ManuscriptIBAW.TypeB.Exceptional.Target.cover_center_card
#print axioms ManuscriptIBAW.TypeB.Exceptional.familyReduction
#print axioms ManuscriptIBAW.TypeB.Exceptional.familyReduction_roots
#print axioms ManuscriptIBAW.TypeB.Exceptional.root_eq_groupRoot
#print axioms ManuscriptIBAW.TypeB.Exceptional.commonFamily
#print axioms ManuscriptIBAW.TypeB.Exceptional.commonCover
#print axioms ManuscriptIBAW.TypeB.Exceptional.commonFamily_root
#print axioms ManuscriptIBAW.TypeB.Exceptional.commonFamily_blockSource
#print axioms ManuscriptIBAW.TypeB.Exceptional.commonFamily_idempotent
#print axioms ManuscriptIBAW.TypeB.Exceptional.commonCover_projection
#print axioms ManuscriptIBAW.TypeB.Exceptional.commonFamily_complete
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.family
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.cover
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.family_root
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.cover_eq_target
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.block_count
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.root_residue
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.rootDown_residue
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.allBlocks
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.completeNatural
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.familyComplete
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.complete
#print axioms ManuscriptIBAW.TypeB.Exceptional.Inputs.projection

#print ManuscriptIBAW.TypeB.Exceptional.AmbientIdempotents
#print ManuscriptIBAW.TypeB.Exceptional.NaturalQuotientTransport
#print ManuscriptIBAW.TypeB.Exceptional.Inputs

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/

#print ManuscriptIBAW.TypeB.Exceptional.B2Sources
#print ManuscriptIBAW.TypeB.Exceptional.BeforeSources
#print ManuscriptIBAW.TypeB.Exceptional.RawInputs
#print ManuscriptIBAW.TypeB.Exceptional.PrincipalSources
#print axioms ManuscriptIBAW.TypeB.Exceptional.B2Sources.toLegacy
#print axioms ManuscriptIBAW.TypeB.Exceptional.RawInputs.allBlocks
#print axioms ManuscriptIBAW.TypeB.Exceptional.PrincipalSources.coherent
#print axioms ModularRep.CurrentSpathFiniteSplittingDescent.current_corollary_2_5_block
#print ModularRep.CurrentSpathFiniteSplittingDescent.Source
