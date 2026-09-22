import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
import ModularRep.BrauerCharacterHomPullback

/-! Defect-zero block uniqueness derives the Q=1 normalization for the
actual retained row. No correspondence-normalization premise is supplied. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter TrivialWeightSource)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierTrivialBlock
open SporadicFi24P3Definition44NamedCarrierQOneCharacters (exists_atOne_from_raw)
open SpathQOneIntermediateBlockTransport

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [MulAction (MulAut G)ᵐᵒᵖ Block]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (O : LocalBlockInductionOperations (p := p) (k := k) (K := K) (G := G) (Block := Block))
variable (compatibility : CanonicalLocalBlockCompatibility iota O)
local notation "inj" => irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota

def DefectZeroReductionBlockSingleton : Prop :=
  letI := O.ambientBlockData.fintypeBlock
  ∀ (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G)) (chi : IBr iota),
    IsBrauerReduction iota d.val chi →
      Subsingleton {psi : IBr iota //
        irreducibleBrauerCharacterBlock iota inj O.ambientBlockData.blocks psi =
          irreducibleBrauerCharacterBlock iota inj O.ambientBlockData.blocks chi}

include compatibility in
theorem qOne_reduction_and_block
    (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
    (hV : V.subgroup = ⊥) :
    letI := O.ambientBlockData.fintypeBlock
    ∃ (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G)) (chi : IBr iota),
      IsBrauerReduction iota d.val chi ∧
      (∀ n : Subgroup.normalizer (V.subgroup : Set G),
        V.localCharacter (QuotientGroup.mk n) = d.val n.val) ∧
      irreducibleBrauerCharacterBlock iota inj O.ambientBlockData.blocks chi =
        O.rawWeightBlock V ∧
      PrimeRegularClassFunction.pullback
        (Subgroup.normalizer (V.subgroup : Set G)).subtype chi.val = source.localBrauer.val := by
  let _ := O.ambientBlockData.fintypeBlock
  let T : TrivialWeightSource (p := p) (X := G) := {
    prime := iota.prime
    trivialRadical := by rw [← hV]; exact V.radical }
  obtain ⟨d, _hAtOne, heval⟩ := exists_atOne_from_raw T V hV
  let N : Subgroup G := Subgroup.normalizer (V.subgroup : Set G)
  let _ : Fintype N := Fintype.ofFinite _
  have hNtop : N = ⊤ := by
    change Subgroup.normalizer (V.subgroup : Set G) = ⊤
    rw [hV]
    exact Subgroup.normalizer_eq_top (⊥ : Subgroup G)
  let e : N ≃* G := (MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv
  have he : e.toMonoidHom = N.subtype := by ext n; rfl
  have hroot : source.normalizerRoot = iota.alongMulEquiv e.symm := by
    rw [source.normalizerRoot_eq, normalizerRootAt_eq_subgroupRoot]
    change subgroupRoot iota N = iota.alongMulEquiv e.symm
    have hN : primeRegularExponent p N ∣ primeRegularExponent p G := by
      simpa only [primeRegularExponent] using
        Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card N) p
    simpa only [commonRoot_self, subgroupRoot] using
      (ofCommonRoot_alongMulEquiv iota.prime iota.toMulEquiv
        (dvd_refl _) hN e.symm).symm
  have hlift : source.normalizerRoot.lift = iota.lift := by
    rw [hroot]
    exact funext (PrimeRegularRootEmbedding.alongMulEquiv_lift iota e.symm)
  let chi : IBr iota := ⟨PrimeRegularClassFunction.pullback e.symm.toMonoidHom
      source.localBrauer.val, by
    obtain ⟨U, hU, hAff⟩ := source.localBrauer.property
    refine ⟨FDRep.of (Representation.pullback U.ρ e.symm.toMonoidHom),
      hU.pullback e.symm.toMonoidHom e.symm.surjective, ?_⟩
    rw [FDRep.of_ρ',
      Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq U.ρ
        source.normalizerRoot iota e.symm.toMonoidHom hlift.symm]
    exact congrArg (PrimeRegularClassFunction.pullback e.symm.toMonoidHom) hAff⟩
  have hred : IsBrauerReduction iota d.val chi := by
    intro g
    let n := PrimeRegularElement.map e.symm.toMonoidHom g
    have hn : n.val.val = g.val :=
      (DFunLike.congr_fun he (e.symm g.val)).symm.trans (e.apply_symm_apply g.val)
    change d.val g.val = source.localBrauer.val n
    exact (congrArg d.val hn.symm).trans
      ((heval n.val).symm.trans (source.localBrauer_reduction n))
  have hphiN : source.localBrauer.val =
      PrimeRegularClassFunction.pullback e.toMonoidHom chi.val := by
    apply PrimeRegularClassFunction.ext
    intro n
    change source.localBrauer.val n = source.localBrauer.val
      (PrimeRegularElement.map e.symm.toMonoidHom (PrimeRegularElement.map e.toMonoidHom n))
    exact (congrArg source.localBrauer.val (Subtype.ext (e.symm_apply_apply n.val))).symm
  let localData := O.inflatedNormalizerBlockData V.subgroup
  let _ := localData.fintypeBlock
  let rootN := source.normalizerRoot
  let phiN := source.localBrauer
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rootN
  let bG := irreducibleBrauerCharacterBlock iota inj O.ambientBlockData.blocks chi
  let bL := O.inflateToNormalizer V.subgroup
    (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero)
  have hLocal : irreducibleBrauerCharacterBlock rootN injN localData.blocks phiN = bL :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer V source
  have hTransported : irreducibleBrauerCharacterBlock rootN injN
      (O.ambientBlockData.blocks.alongMulEquiv e.symm) phiN = bG :=
    irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
      iota inj rootN injN e.symm O.ambientBlockData.blocks chi phiN hlift hphiN
  have hCatalogue : (O.ambientBlockData.catalogue.alongMulEquiv e.symm).centralCharacter bG =
      localData.catalogue.centralCharacter bL := by
    rw [← hTransported, ← hLocal]
    exact centralCharacter_eq_of_same_IBr rootN injN
      (O.ambientBlockData.blocks.alongMulEquiv e.symm) localData.blocks
      (O.ambientBlockData.catalogue.alongMulEquiv e.symm) localData.catalogue phiN
  have hSelf := blockInducesTo_self_of_equiv_subtype
    (k := k) (H := N) O.ambientBlockData.blocks O.ambientBlockData.catalogue e he bG
  have hActual : BlockInducesTo N localData.catalogue O.ambientBlockData.catalogue bL bG := by
    simpa only [BlockInducesTo, hCatalogue] using hSelf
  have hInduced : bG = O.rawWeightBlock V :=
    eq_inducedBlock_of_blockInducesTo N localData.catalogue O.ambientBlockData.catalogue bL
      (O.blockInductionDefined V) hActual
  refine ⟨d, chi, hred, heval, hInduced, ?_⟩
  simpa only [he] using hphiN.symm

include compatibility in
theorem qOne_localBrauer_of_block_singleton
    (singleton : DefectZeroReductionBlockSingleton iota O)
    (phi : IBr iota) (V : CharacterWeight p K G)
    (source : CanonicalRawReduction iota V) (hV : V.subgroup = ⊥)
    (hblock : letI := O.ambientBlockData.fintypeBlock
      irreducibleBrauerCharacterBlock iota inj O.ambientBlockData.blocks phi = O.rawWeightBlock V) :
    (∃ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G),
      IsBrauerReduction iota d.val phi ∧
      ∀ n : Subgroup.normalizer (V.subgroup : Set G),
        V.localCharacter (QuotientGroup.mk n) = d.val n.val) ∧
    PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (V.subgroup : Set G)).subtype phi.val = source.localBrauer.val := by
  let _ := O.ambientBlockData.fintypeBlock
  obtain ⟨d, chi, hred, heval, hblockChi, hpull⟩ :=
    qOne_reduction_and_block iota O compatibility V source hV
  have hphiChi : phi = chi := by
    let _ := singleton d chi hred
    have h : (⟨phi, hblock.trans hblockChi.symm⟩ :
        {psi : IBr iota //
          irreducibleBrauerCharacterBlock iota inj O.ambientBlockData.blocks psi =
            irreducibleBrauerCharacterBlock iota inj O.ambientBlockData.blocks chi}) =
          ⟨chi, rfl⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val h
  subst phi
  exact ⟨⟨d, hred, heval⟩, hpull⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
