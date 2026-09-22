import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralBlockKernel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient
import ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-! The raw matched weight's own local character descends through the
global character's central kernel. Actual block induction is derived from
the literal operations and common block. The local kernel and character
constancy are conclusions, not source fields. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnLocalKernel

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
variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))

include compatibility hrawBlock hprimeTo in
theorem own_local_kernel :
    (centralCharacterKernel P psi).subgroupOf (Subgroup.normalizer (V.subgroup : Set P.H)) ≤
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ.ker := by
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData V.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := localData.fintypeBlock
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let Z0 := centralCharacterKernel P psi
  let : Invertible (Fintype.card Z0 : P.k) := invertibleOfNonzero (by
    intro h
    apply hprimeTo
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
  exact local_central_kernel_of_blockInducesTo N Z0
    (inf_le_left.trans (Subgroup.center_le_normalizer (V.subgroup : Set P.H))) inf_le_left
    localData.catalogue O.ambientBlockData.catalogue hbase rhoN rhoG
    (block_smul_of_affording source.normalizerRoot injN localData.blocks source.localBrauer
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer)
      (Classical.choose_spec source.localBrauer.2).1
      (chosenIBrRepresentation_character source.normalizerRoot source.localBrauer))
    (block_smul_of_affording P.iota P.irreducibleBrauerInjective O.ambientBlockData.blocks psi.1
      (chosenBrauerRepresentation P psi) (chosenBrauerRepresentation_irreducible P psi)
      (chosenBrauerRepresentation_character P psi))
    inf_le_right

include source compatibility hrawBlock hprimeTo in
theorem own_weight_character_constant_on_quotient_kernel :
    ∀ x : (qW (centralCharacterKernel P psi) V.subgroup).ker,
      V.localCharacter (x : NormalizerQuotient V.subgroup) = V.localCharacter 1 := by
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let Z0 := centralCharacterKernel P psi
  let ZN := Z0.subgroupOf N
  have hZ0central : Z0 ≤ Subgroup.center P.H := inf_le_left
  have hZ0N : Z0 ≤ N := hZ0central.trans (Subgroup.center_le_normalizer (V.subgroup : Set P.H))
  have hcard : Nat.card ZN = Nat.card Z0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ0N).toEquiv
  have hcoprime : (Nat.card ZN).Coprime P.p := by
    rw [hcard]
    exact (P.iota.prime.coprime_iff_not_dvd.mpr hprimeTo).symm
  have hkernel := own_local_kernel P psi V source compatibility hrawBlock hprimeTo
  intro x
  have hx : (x : NormalizerQuotient V.subgroup) ∈
      ZN.map (QuotientGroup.mk' (V.subgroup.subgroupOf N)) := by
    rw [← qW_ker_eq_localCentralKernel_map Z0 V.subgroup hZ0central]
    exact x.2
  obtain ⟨y, hy, hxy⟩ := hx
  have hyregular : IsPrimeRegular P.p y :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard ZN hy) hcoprime
  let yp : PrimeRegularElement (G := N) P.p := ⟨y, hyregular⟩
  let onep : PrimeRegularElement (G := N) P.p := ⟨1, isPrimeRegular_one⟩
  have hvalues : source.localBrauer.1 yp = source.localBrauer.1 onep := by
    rw [chosenIBrRepresentation_character source.normalizerRoot source.localBrauer]
    exact brauer_apply_eq_one_of_mem_ker _ _ yp (hkernel hy)
  calc
    V.localCharacter (x : NormalizerQuotient V.subgroup) =
        V.localCharacter (QuotientGroup.mk' (V.subgroup.subgroupOf N) y) :=
      congrArg V.localCharacter hxy.symm
    _ = source.localBrauer.1 yp := source.localBrauer_reduction yp
    _ = source.localBrauer.1 onep := hvalues
    _ = V.localCharacter 1 := by
      simpa only [onep, map_one] using (source.localBrauer_reduction onep).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnLocalKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
