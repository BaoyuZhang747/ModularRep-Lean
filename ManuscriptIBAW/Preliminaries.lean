import ModularRep.CentralCharacterBlockSector
import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.CurrentSpathCriterion
import ModularRep.CurrentSpathDescent
import ModularRep.PaperProofs.CurrentFiniteSplittingAssembly
import ModularRep.PaperProofs.CurrentCentralQuotientBijection
import ModularRep.PaperProofs.CurrentCentralQuotientReturnAdapter

/-!
# Central characters, the inductive condition and central quotients

This file states the general deductions used in Section 2 under their
explicit assumptions.

Theorem 2.3 uses Späth's published equivalence on the full covering group
and its central character quotient. The modular block triple relation
enters through BlockTripleSourceSemantics. Its identification with the
standard relation and the required transport laws remain external.
Remark 2.4 uses the published passage from block conditions to the full
inductive condition, in the form for all blocks. Both published passages
are explicit assumptions here.

For Corollary 2.5, the map from the covering group to the simple group is
constructed and the published descent theorem is applied to that map. For
Lemma 2.6, the proof transports the given block bijection through the
central core quotient, proves equivariance and applies the published result
on normal kernels to the same character and weight. It assumes no upstairs
bijection or modular character triple conclusion.
-/

namespace ManuscriptIBAW.Preliminaries

namespace CentralSectors

export ModularRep (IsCentralCharacterSector)
export ModularRep.IsPrimitiveCentralIdempotent
  (existsUnique_centralCharacterSector centralCharacterSector
   centralCharacterSector_isSector)
export Representation
  (centralCharacter_eq_of_isCentralCharacterSector
   primitiveCentralIdempotentSector_eq_centralCharacter)
export ModularRep.LiteralPrimitiveBlock
  (rightMulAction_smul_centralCharacterSector inner_smul)

end CentralSectors

namespace SpathCriterion

export ModularRep.CurrentSpathCriterion
  (FullCover PairData HattedPairJoins ClauseIII TripleCondition Theorem44Source
   current_theorem_2_3 clauseIII_to_actual_triples actual_triples_to_clauseIII)

end SpathCriterion

namespace BlockFamilies

export ModularRep.PaperProofs.CurrentFiniteSplittingAssembly (Source fullFamily)

end BlockFamilies

namespace Descent

export ModularRep.CurrentSpathDescent
  (FullCoverPrimeToDiagram FullCoverInflation Coefficients PhysicalFamilySource
   CoherentToDefinition35Source Proposition46Theorem44Source
   current_corollary_2_5_coherent current_corollary_2_5)

end Descent

namespace CentralCore

export ModularRep.PaperProofs.CurrentCentralQuotientBijection
  (core_le_raw rawLocalQuotientEquiv quotientRawWeight quotientRawWeight_character
   ownReduction_inflation CentralBlockSource NormalPair QuotientNormalPair
   CompatibleBijection TripleQuotientSource sameWeight_relation_upward
   lemma_2_6_compatibleBijection)
export ModularRep.PaperProofs.CurrentCentralQuotientReturnAdapter
  (FiniteMatchedCompatibleSource PhysicalReindexing Definition35CompatibleIdentification
   returnCompatibleThroughCentralQuotient CentralReturnInputs)

end CentralCore

end ManuscriptIBAW.Preliminaries

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
