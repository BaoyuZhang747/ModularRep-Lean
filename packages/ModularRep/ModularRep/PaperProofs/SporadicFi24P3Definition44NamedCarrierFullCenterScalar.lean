import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralBlockKernel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient
import ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-! Actual block induction identifies the modular Schur scalars on the
full centre for the matched global and local characters. Their block
relation is derived from the fixed-root operations and the same raw match. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCenterScalar

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralBlockKernel
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

universe u
local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H) (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))

local instance globalIrreducible : Representation.IsIrreducible (chosenBrauerRepresentation P psi).ρ :=
  chosenBrauerRepresentation_irreducible P psi
local instance localIrreducible : Representation.IsIrreducible
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ :=
  (Classical.choose_spec source.localBrauer.2).1

include compatibility hrawBlock hcenter in
theorem full_center_scalar_eq
    (z : (Subgroup.center P.H).subgroupOf (Subgroup.normalizer (V.subgroup : Set P.H))) :
    Representation.centralCharacter
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
      ((Subgroup.center P.H).subgroupOf (Subgroup.normalizer (V.subgroup : Set P.H)))
      (subgroupOf_le_center _ _ le_rfl) z =
    Representation.centralCharacter (chosenBrauerRepresentation P psi).ρ
      (Subgroup.center P.H) le_rfl
      (Subgroup.subgroupOfEquivOfLe (Subgroup.center_le_normalizer (V.subgroup : Set P.H)) z) := by
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData V.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := localData.fintypeBlock
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let Z0 := Subgroup.center P.H
  let : Invertible (Fintype.card Z0 : P.k) := invertibleOfNonzero (by
    intro h
    apply hcenter
    simpa only [Nat.card_eq_fintype_card] using
      (CharP.cast_eq_zero_iff P.k P.p (Fintype.card Z0)).mp h)
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding source.normalizerRoot
  have hlocal : irreducibleBrauerCharacterBlock source.normalizerRoot injN
      localData.blocks source.localBrauer =
        O.inflateToNormalizer V.subgroup (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero) :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer V source
  have hbase : BlockInducesTo N localData.catalogue O.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock source.normalizerRoot injN localData.blocks source.localBrauer)
      (irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
        O.ambientBlockData.blocks psi.1) := by
    rw [hlocal, ← hrawBlock]
    exact inducedBlock_spec N localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer V.subgroup (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      (O.blockInductionDefined V)
  let rhoN := (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
  let rhoG := (chosenBrauerRepresentation P psi).ρ
  let : Representation.IsIrreducible rhoN := (Classical.choose_spec source.localBrauer.2).1
  let : Representation.IsIrreducible rhoG := chosenBrauerRepresentation_irreducible P psi
  exact Representation.centralCharacter_apply_eq_of_blockInducesTo N Z0
    (Subgroup.center_le_normalizer (V.subgroup : Set P.H)) le_rfl
    (subgroupOf_le_center N Z0 le_rfl)
    localData.catalogue O.ambientBlockData.catalogue hbase rhoN rhoG
    (block_smul_of_affording source.normalizerRoot injN localData.blocks source.localBrauer
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer)
      (Classical.choose_spec source.localBrauer.2).1
      (chosenIBrRepresentation_character source.normalizerRoot source.localBrauer))
    (block_smul_of_affording P.iota P.irreducibleBrauerInjective O.ambientBlockData.blocks psi.1
      (chosenBrauerRepresentation P psi) (chosenBrauerRepresentation_irreducible P psi)
      (chosenBrauerRepresentation_character P psi))
    z

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCenterScalar


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
