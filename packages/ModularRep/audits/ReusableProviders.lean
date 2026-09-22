import ModularRep.CharacterWeightCentralRestriction
import ModularRep.BlockInductionCentralIdempotentSupport
import ModularRep.CentralCharacterBlockInductionRestriction
import ModularRep.LiteralOrdinaryBlockReduction
import ModularRep.PrimeRegularRootEmbeddingPQuotient
import ModularRep.BrauerLocalExtensionInnerTransport
import ModularRep.NavarroCoveringBrauerExtension
import ModularRep.NavarroBrauerRestrictionCovering
import ModularRep.CyclicBrauerTopBlockFromBaseInduction
import ModularRep.AxiomGate

/-!
# Release policy for nine reusable providers

This release policy mechanically checks the stable modules and their public
APIs. It does not prove the Navarro source interfaces or any concrete Fischer
instance; those remain explicit E1/U inputs at application sites.
-/

assert_only_standard_axioms ModularRep.CharacterWeight.centralRestriction
assert_only_standard_axioms ModularRep.CharacterWeight.centralRestriction_one
assert_only_standard_axioms ModularRep.CharacterWeight.centralRestriction_rightTwist_of_fixed
assert_only_standard_axioms ModularRep.CharacterWeight.centralRestriction_inner
assert_only_standard_axioms ModularRep.CharacterWeight.isoCentralRestriction
assert_only_standard_axioms ModularRep.CharacterWeight.isoCentralRestriction_inner
assert_only_standard_axioms ModularRep.CharacterWeight.classCentralRestriction
assert_only_standard_axioms ModularRep.CharacterWeight.centralRestriction_eq_of_class_eq
assert_only_standard_axioms ModularRep.CharacterWeight.centralRestriction_formula_of_class_eq

assert_only_standard_axioms ModularRep.BlockCentralCharacterCatalogue.centralIdempotent_value_one_iff
assert_only_standard_axioms ModularRep.blockInducesTo_preserves_centralIdempotentSupport

assert_only_standard_axioms ModularRep.subgroupOf_le_center
assert_only_standard_axioms ModularRep.card_subgroupOf_eq_of_le
assert_only_standard_axioms ModularRep.invertibleCardSubgroupOfOfLe
assert_only_standard_axioms ModularRep.coeffRestrict_centralCharacterIdempotent
assert_only_standard_axioms ModularRep.centralCharacterIdempotentInCenter
assert_only_standard_axioms ModularRep.centralCharacterIdempotentInCenter_coe
assert_only_standard_axioms ModularRep.centerCoeffRestrict_centralCharacterIdempotentInCenter
assert_only_standard_axioms ModularRep.coeffRestrict_centralCharacterIdempotent_isIdempotentElem
assert_only_standard_axioms Representation.centralCharacter_eq_comp_of_blockInducesTo
assert_only_standard_axioms Representation.centralCharacter_apply_eq_of_blockInducesTo

assert_only_standard_axioms ModularRep.LiteralOrdinaryPBlockSource.ordinaryBlock_eq_literalBrauerBlock_of_reduction

assert_only_standard_axioms ModularRep.PrimeRegularRootEmbeddingPQuotient.transport
assert_only_standard_axioms ModularRep.PrimeRegularRootEmbeddingPQuotient.transport_lift
assert_only_standard_axioms ModularRep.PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq
assert_only_standard_axioms ModularRep.PrimeRegularRootEmbeddingPQuotient.ofPQuotient
assert_only_standard_axioms ModularRep.PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift

assert_only_standard_axioms Representation.Extension.BrauerCharacterExtensionWitness.alongEquivalences
assert_only_standard_axioms Representation.Extension.BrauerCharacterExtensionWitness.alongEquivalences_value
assert_only_standard_axioms Representation.Extension.BrauerCharacterExtensionWitness.inner_transport_value
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_coe
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_symm_coe
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.localBaseEquivOfConjEq
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.localBaseEquivOfConjEq_square
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.IntermediateNormalizer
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.intermediateInclusion
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_square
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_ambient_square
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.localExtensionOfConjEq
assert_only_standard_axioms ModularRep.InnerNormalizerTransport.localExtensionOfConjEq_root_lifts

assert_only_standard_axioms ModularRep.NavarroCoveringBrauerExtension.BrauerOccursInRestriction
assert_only_standard_axioms ModularRep.NavarroCoveringBrauerExtension.Navarro9495BrauerCoveringPrinciple
assert_only_standard_axioms ModularRep.NavarroCoveringBrauerExtension.Navarro820CyclicBrauerTwistPrinciple
assert_only_standard_axioms ModularRep.NavarroCoveringBrauerExtension.restriction_eq_of_cyclic_twist
assert_only_standard_axioms ModularRep.NavarroCoveringBrauerExtension.exists_extension_in_covering_block

assert_only_standard_axioms ModularRep.NavarroBrauerRestrictionCovering.Navarro9295BrauerRestrictionCoveringPrinciple
assert_only_standard_axioms ModularRep.NavarroBrauerRestrictionCovering.brauerOccursInRestriction_of_pullback_eq
assert_only_standard_axioms ModularRep.NavarroBrauerRestrictionCovering.centralCharacterCovers_of_extension

assert_only_standard_axioms ModularRep.CyclicBrauerTopBlockFromBaseInduction.exists_global_extension_with_induced_block

assert_no_direct_conclusion_hypothesis ModularRep.CharacterWeight.centralRestriction_one
assert_no_direct_conclusion_hypothesis ModularRep.CharacterWeight.centralRestriction_rightTwist_of_fixed
assert_no_direct_conclusion_hypothesis ModularRep.CharacterWeight.centralRestriction_inner
assert_no_direct_conclusion_hypothesis ModularRep.CharacterWeight.isoCentralRestriction_inner
assert_no_direct_conclusion_hypothesis ModularRep.CharacterWeight.centralRestriction_eq_of_class_eq
assert_no_direct_conclusion_hypothesis ModularRep.CharacterWeight.centralRestriction_formula_of_class_eq
assert_no_direct_conclusion_hypothesis ModularRep.BlockCentralCharacterCatalogue.centralIdempotent_value_one_iff
assert_no_direct_conclusion_hypothesis ModularRep.blockInducesTo_preserves_centralIdempotentSupport
assert_no_direct_conclusion_hypothesis ModularRep.subgroupOf_le_center
assert_no_direct_conclusion_hypothesis ModularRep.card_subgroupOf_eq_of_le
assert_no_direct_conclusion_hypothesis ModularRep.coeffRestrict_centralCharacterIdempotent
assert_no_direct_conclusion_hypothesis ModularRep.centralCharacterIdempotentInCenter_coe
assert_no_direct_conclusion_hypothesis ModularRep.centerCoeffRestrict_centralCharacterIdempotentInCenter
assert_no_direct_conclusion_hypothesis ModularRep.coeffRestrict_centralCharacterIdempotent_isIdempotentElem
assert_no_direct_conclusion_hypothesis Representation.centralCharacter_eq_comp_of_blockInducesTo
assert_no_direct_conclusion_hypothesis Representation.centralCharacter_apply_eq_of_blockInducesTo
assert_no_direct_conclusion_hypothesis ModularRep.LiteralOrdinaryPBlockSource.ordinaryBlock_eq_literalBrauerBlock_of_reduction
assert_no_direct_conclusion_hypothesis ModularRep.PrimeRegularRootEmbeddingPQuotient.transport_lift
assert_no_direct_conclusion_hypothesis ModularRep.PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq
assert_no_direct_conclusion_hypothesis ModularRep.PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
assert_no_direct_conclusion_hypothesis Representation.Extension.BrauerCharacterExtensionWitness.alongEquivalences_value
assert_no_direct_conclusion_hypothesis Representation.Extension.BrauerCharacterExtensionWitness.inner_transport_value
assert_no_direct_conclusion_hypothesis ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_coe
assert_no_direct_conclusion_hypothesis ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_symm_coe
assert_no_direct_conclusion_hypothesis ModularRep.InnerNormalizerTransport.localBaseEquivOfConjEq_square
assert_no_direct_conclusion_hypothesis ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_square
assert_no_direct_conclusion_hypothesis ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_ambient_square
assert_no_direct_conclusion_hypothesis ModularRep.InnerNormalizerTransport.localExtensionOfConjEq_root_lifts
assert_no_direct_conclusion_hypothesis ModularRep.NavarroCoveringBrauerExtension.restriction_eq_of_cyclic_twist
assert_no_direct_conclusion_hypothesis ModularRep.NavarroCoveringBrauerExtension.exists_extension_in_covering_block
assert_no_direct_conclusion_hypothesis ModularRep.NavarroBrauerRestrictionCovering.brauerOccursInRestriction_of_pullback_eq
assert_no_direct_conclusion_hypothesis ModularRep.NavarroBrauerRestrictionCovering.centralCharacterCovers_of_extension
assert_no_direct_conclusion_hypothesis ModularRep.CyclicBrauerTopBlockFromBaseInduction.exists_global_extension_with_induced_block

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    String.toName "ModularRep.CharacterWeightCentralRestriction",
    String.toName "ModularRep.BlockInductionCentralIdempotentSupport",
    String.toName "ModularRep.CentralCharacterBlockInductionRestriction",
    String.toName "ModularRep.LiteralOrdinaryBlockReduction",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient",
    String.toName "ModularRep.BrauerLocalExtensionInnerTransport",
    String.toName "ModularRep.NavarroCoveringBrauerExtension",
    String.toName "ModularRep.NavarroBrauerRestrictionCovering",
    String.toName "ModularRep.CyclicBrauerTopBlockFromBaseInduction"]
  let allowed : Lean.NameSet := Lean.NameSet.ofList [
    String.toName "propext",
    String.toName "Classical.choice",
    String.toName "Quot.sound"]
  for target in targets do
    let some idx := env.getModuleIdx? target | throwError "Audit target module absent: {target}"
    let some data := env.header.moduleData[idx.toNat]? | throwError "Audit module data absent: {target}"
    if data.constNames.isEmpty then throwError "Audit module has no serialized constants: {target}"
    let mut publicProofs : Nat := 0
    for name in data.constNames do
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Module {target} constant {name} depends on forbidden axiom {axiomName}"
      let publicProof ← liftTermElabM do
        let info ← getConstInfo name
        return (← isProp info.type) && !Lean.isPrivateName name && !name.isInternal
      if publicProof then
        publicProofs := publicProofs + 1
        liftTermElabM do
          let info ← getConstInfo name
          forallTelescope info.type fun xs conclusion => do
            for x in xs do
              let hypothesisType ← inferType x
              if ← isDefEq hypothesisType conclusion then
                throwError "Public proof {name} has a direct conclusion hypothesis: {hypothesisType}"
      logInfo m!"MODULE_CONSTANT {target} {name} publicProof={publicProof}"
    logInfo m!"MODULE_AXIOMS_PASS {target} constants={data.constNames.size} publicProofs={publicProofs}"

open Lean Meta Elab Command in
run_cmd do
  let intended : Array Name := #[
    String.toName "ModularRep.CharacterWeight.centralRestriction",
    String.toName "ModularRep.CharacterWeight.centralRestriction_one",
    String.toName "ModularRep.CharacterWeight.centralRestriction_rightTwist_of_fixed",
    String.toName "ModularRep.CharacterWeight.centralRestriction_inner",
    String.toName "ModularRep.CharacterWeight.isoCentralRestriction",
    String.toName "ModularRep.CharacterWeight.isoCentralRestriction_inner",
    String.toName "ModularRep.CharacterWeight.classCentralRestriction",
    String.toName "ModularRep.CharacterWeight.centralRestriction_eq_of_class_eq",
    String.toName "ModularRep.CharacterWeight.centralRestriction_formula_of_class_eq",
    String.toName "ModularRep.BlockCentralCharacterCatalogue.centralIdempotent_value_one_iff",
    String.toName "ModularRep.blockInducesTo_preserves_centralIdempotentSupport",
    String.toName "ModularRep.subgroupOf_le_center",
    String.toName "ModularRep.card_subgroupOf_eq_of_le",
    String.toName "ModularRep.invertibleCardSubgroupOfOfLe",
    String.toName "ModularRep.coeffRestrict_centralCharacterIdempotent",
    String.toName "ModularRep.centralCharacterIdempotentInCenter",
    String.toName "ModularRep.centralCharacterIdempotentInCenter_coe",
    String.toName "ModularRep.centerCoeffRestrict_centralCharacterIdempotentInCenter",
    String.toName "ModularRep.coeffRestrict_centralCharacterIdempotent_isIdempotentElem",
    String.toName "Representation.centralCharacter_eq_comp_of_blockInducesTo",
    String.toName "Representation.centralCharacter_apply_eq_of_blockInducesTo",
    String.toName "ModularRep.LiteralOrdinaryPBlockSource.ordinaryBlock_eq_literalBrauerBlock_of_reduction",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.transport",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.transport_lift",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.ofPQuotient",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift",
    String.toName "Representation.Extension.BrauerCharacterExtensionWitness.alongEquivalences",
    String.toName "Representation.Extension.BrauerCharacterExtensionWitness.alongEquivalences_value",
    String.toName "Representation.Extension.BrauerCharacterExtensionWitness.inner_transport_value",
    String.toName "ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq",
    String.toName "ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_coe",
    String.toName "ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_symm_coe",
    String.toName "ModularRep.InnerNormalizerTransport.localBaseEquivOfConjEq",
    String.toName "ModularRep.InnerNormalizerTransport.localBaseEquivOfConjEq_square",
    String.toName "ModularRep.InnerNormalizerTransport.IntermediateNormalizer",
    String.toName "ModularRep.InnerNormalizerTransport.intermediateInclusion",
    String.toName "ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq",
    String.toName "ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_square",
    String.toName "ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_ambient_square",
    String.toName "ModularRep.InnerNormalizerTransport.localExtensionOfConjEq",
    String.toName "ModularRep.InnerNormalizerTransport.localExtensionOfConjEq_root_lifts",
    String.toName "ModularRep.NavarroCoveringBrauerExtension.BrauerOccursInRestriction",
    String.toName "ModularRep.NavarroCoveringBrauerExtension.Navarro9495BrauerCoveringPrinciple",
    String.toName "ModularRep.NavarroCoveringBrauerExtension.Navarro820CyclicBrauerTwistPrinciple",
    String.toName "ModularRep.NavarroCoveringBrauerExtension.restriction_eq_of_cyclic_twist",
    String.toName "ModularRep.NavarroCoveringBrauerExtension.exists_extension_in_covering_block",
    String.toName "ModularRep.NavarroBrauerRestrictionCovering.Navarro9295BrauerRestrictionCoveringPrinciple",
    String.toName "ModularRep.NavarroBrauerRestrictionCovering.brauerOccursInRestriction_of_pullback_eq",
    String.toName "ModularRep.NavarroBrauerRestrictionCovering.centralCharacterCovers_of_extension",
    String.toName "ModularRep.CyclicBrauerTopBlockFromBaseInduction.exists_global_extension_with_induced_block"]
  for name in intended do
    liftTermElabM do
      let info ← getConstInfo name
      logInfo m!"NAMED_EXPORT_TYPE {name}: {info.type}"
  let proofs : Array Name := #[
    String.toName "ModularRep.CharacterWeight.centralRestriction_one",
    String.toName "ModularRep.CharacterWeight.centralRestriction_rightTwist_of_fixed",
    String.toName "ModularRep.CharacterWeight.centralRestriction_inner",
    String.toName "ModularRep.CharacterWeight.isoCentralRestriction_inner",
    String.toName "ModularRep.CharacterWeight.centralRestriction_eq_of_class_eq",
    String.toName "ModularRep.CharacterWeight.centralRestriction_formula_of_class_eq",
    String.toName "ModularRep.BlockCentralCharacterCatalogue.centralIdempotent_value_one_iff",
    String.toName "ModularRep.blockInducesTo_preserves_centralIdempotentSupport",
    String.toName "ModularRep.subgroupOf_le_center",
    String.toName "ModularRep.card_subgroupOf_eq_of_le",
    String.toName "ModularRep.coeffRestrict_centralCharacterIdempotent",
    String.toName "ModularRep.centralCharacterIdempotentInCenter_coe",
    String.toName "ModularRep.centerCoeffRestrict_centralCharacterIdempotentInCenter",
    String.toName "ModularRep.coeffRestrict_centralCharacterIdempotent_isIdempotentElem",
    String.toName "Representation.centralCharacter_eq_comp_of_blockInducesTo",
    String.toName "Representation.centralCharacter_apply_eq_of_blockInducesTo",
    String.toName "ModularRep.LiteralOrdinaryPBlockSource.ordinaryBlock_eq_literalBrauerBlock_of_reduction",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.transport_lift",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq",
    String.toName "ModularRep.PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift",
    String.toName "Representation.Extension.BrauerCharacterExtensionWitness.alongEquivalences_value",
    String.toName "Representation.Extension.BrauerCharacterExtensionWitness.inner_transport_value",
    String.toName "ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_coe",
    String.toName "ModularRep.InnerNormalizerTransport.normalizerEquivOfConjEq_symm_coe",
    String.toName "ModularRep.InnerNormalizerTransport.localBaseEquivOfConjEq_square",
    String.toName "ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_square",
    String.toName "ModularRep.InnerNormalizerTransport.intermediateNormalizerEquivOfConjEq_ambient_square",
    String.toName "ModularRep.InnerNormalizerTransport.localExtensionOfConjEq_root_lifts",
    String.toName "ModularRep.NavarroCoveringBrauerExtension.restriction_eq_of_cyclic_twist",
    String.toName "ModularRep.NavarroCoveringBrauerExtension.exists_extension_in_covering_block",
    String.toName "ModularRep.NavarroBrauerRestrictionCovering.brauerOccursInRestriction_of_pullback_eq",
    String.toName "ModularRep.NavarroBrauerRestrictionCovering.centralCharacterCovers_of_extension",
    String.toName "ModularRep.CyclicBrauerTopBlockFromBaseInduction.exists_global_extension_with_induced_block"]
  for name in proofs do
    liftTermElabM do
      let info ← getConstInfo name
      match info with
      | .thmInfo theoremInfo =>
          let actual ← inferType theoremInfo.value
          unless ← isDefEq actual theoremInfo.type do
            throwError "Proof value/type mismatch: {name}"
          logInfo m!"NAMED_PROOF_VALUE_PASS {name}"
      | _ => throwError "Intended theorem missing proof value: {name}"


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
