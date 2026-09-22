import ModularRep.AxiomGate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedIntegration

open Lean Meta Elab Command

set_option maxHeartbeats 4000000

-- Inspect both types and values throughout the project declaration graph.
-- Foundation declarations precede this project and cannot depend on its sources.
elab "assert_p3_radical_support_dependencies " ns:ident+ : command => do
  let roots ← ns.mapM fun n =>
    liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let spelling := name.toString
    if spelling.contains "Fi24ThreeBlockSource" || spelling.contains "RemainingCarrierTransport" || spelling.contains "SporadicFi24TrivialSectorQuotientSpecialisation" || spelling.startsWith "ModularRep.NavarroLocalReductionInflationBlockCompatibility.Source" ||
        spelling == "ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport.baseBlockInducesTo_ofOperations_centerless_of_compatibility" ||
        spelling == "ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport.selectedBaseLocalBlock_eq_source_of_compatibility" ||
        spelling.endsWith ".positiveQSourceNormalizerBlockSupport_of_compatibility" ||
        spelling.startsWith "ModularRep.PaperProofs.TypeBCentralKernelWeightTransport.kernel_le_radical" ||
        spelling.startsWith "ModularRep.PaperProofs.TypeBCentralKernelWeightTransport.localEquiv" ||
        spelling.startsWith "ModularRep.PaperProofs.TypeBCentralKernelWeightTransport.descend" ||
        spelling.startsWith "ModularRep.PaperProofs.TypeBCentralKernelWeightTransport.lift" then
      throwError m!"A selected endpoint reaches withdrawn declaration {name}"
    if let some info := env.find? name then
      for dependency in info.getUsedConstantsAsSet.toArray do
        if let some idx := env.getModuleIdxFor? dependency then
          let owner := moduleNames[idx]!.toString
          if owner.startsWith "ModularRep." || owner.startsWith "Formalisation." then
            todo := todo.push dependency
    else
      throwError m!"Missing declaration during dependency inspection: {name}"
  logInfo m!"PASS: {roots.size} endpoints; inspected {seen.toArray.size} project declarations; no unrestricted local block source, three-block census, old trivial-sector factory, or Type B p-kernel weight transport."

assert_p3_radical_support_dependencies
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.Inputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.realise
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.ExceptionalInputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.PublishedTwentyTwoInputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.boundary_pair_mem_iff
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.boundary_name_of_mem
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.exceptionalResult
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.proposition57Model
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.proposition57_from_external_inputs
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.allResults
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.modelsOfInputs
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly.sporadic_from_external_inputs
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedBlockDefinition41.BlockDefinition41Witness.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedBlockDefinition41.BlockCertificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefectFour.BlockRealization.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefectFour.ClassificationData.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefectFour.ClassificationConsequences.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefectFour.PublishedBranchPrinciples.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefectFour.defect_four_block_certificate
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCentralSectorAssembly.SectorInputs.mk
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCentralSectorAssembly.assemble
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCentralSectorAssembly.definition41_from_sector_inputs
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedEquivariantReplacement.centerless_partition_and_comparison
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedEquivariantReplacement.central_two_partition_and_comparison
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedEquivariantReplacement.faithful_partition_and_comparison
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedEquivariantReplacement.outer_trivial_partition_and_comparison
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalCompleteCollapse.exists_definition41_of_numerical
  ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse.exists_definition41_of_numerical
  Formalisation.BlockCancellation.cancel_equivariant_equiv_of_parts
  Formalisation.BlockCancellation.cancel_exchanged_blocks_preserving


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
