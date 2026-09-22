import ModularRep.BrauerCharacterEquivTransport
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily

/-! Canonical local availability at the trivial radical supplies the global
reduction of each original defect-zero ordinary character at the same root
embedding. Injectivity of regular restriction remains a separate input. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalGlobalDefectZeroReduction

open ModularRep ModularRep.CharacterWeight
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource GlobalDefectZeroCharacter
    TrivialWeightSource trivialNormalizerEquiv)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
  (LocalCanonicalAvailability)

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]

theorem existsUnique_reduction_of_canonical_atOne
    (iota : PrimeRegularRootEmbedding p k K G)
    (T : TrivialWeightSource (p := p) (X := G))
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G))
    (source : CanonicalRawReduction iota (T.rawAtOne d)) :
    ∃! chi : IBr iota, IsBrauerReduction iota d.val chi := by
  let N : Subgroup G := Subgroup.normalizer ((⊥ : Subgroup G) : Set G)
  let e : N ≃* G := trivialNormalizerEquiv
  have he : e.toMonoidHom = N.subtype := by
    ext n
    rfl
  have hroot : source.normalizerRoot.alongMulEquiv e = iota := by
    rw [source.normalizerRoot_eq, normalizerRootAt_eq_subgroupRoot]
    change (subgroupRoot iota N).alongMulEquiv e = iota
    have hN : primeRegularExponent p N ∣ primeRegularExponent p G := by
      simpa only [primeRegularExponent] using
        Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card N) p
    simpa only [subgroupRoot, commonRoot_self] using
      ofCommonRoot_alongMulEquiv iota.prime iota.toMulEquiv hN (dvd_refl _) e
  let chi : IBr iota :=
    ⟨PrimeRegularClassFunction.pullback e.symm.toMonoidHom source.localBrauer.val, by
      have hchi := IrreducibleBrauerCharacter.pullback_isIrreducibleBrauerCharacter
        source.normalizerRoot e source.localBrauer
      rw [hroot] at hchi
      exact hchi⟩
  have hred : IsBrauerReduction iota d.val chi := by
    intro g
    let n := PrimeRegularElement.map e.symm.toMonoidHom g
    have hn : n.val.val = g.val :=
      (DFunLike.congr_fun he (e.symm g.val)).symm.trans (e.apply_symm_apply g.val)
    have hlocal := source.localBrauer_reduction n
    change d.val n.val.val = source.localBrauer.val n at hlocal
    change d.val g.val = source.localBrauer.val n
    exact (congrArg d.val hn.symm).trans hlocal
  refine ⟨chi, hred, ?_⟩
  intro psi hpsi
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro g
  exact (hpsi g).symm.trans (hred g)

theorem existsUnique_reduction_of_availability
    (iota : PrimeRegularRootEmbedding p k K G)
    (availability : LocalCanonicalAvailability iota)
    (T : TrivialWeightSource (p := p) (X := G))
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G)) :
    ∃! chi : IBr iota, IsBrauerReduction iota d.val chi := by
  have hs : Nonempty (CanonicalRawReduction iota (T.rawAtOne d)) :=
    availability ⟨⊥, T.trivialRadical⟩
      ⟨(T.rawAtOne d).localCharacter, (T.rawAtOne d).defectZero⟩
  obtain ⟨source⟩ := hs
  exact existsUnique_reduction_of_canonical_atOne iota T d source

theorem defectZeroReductionSourceOfAvailability
    (iota : PrimeRegularRootEmbedding p k K G)
    (availability : LocalCanonicalAvailability iota)
    (T : TrivialWeightSource (p := p) (X := G))
    (hregular :
      ∀ d d' : GlobalDefectZeroCharacter (p := p) (K := K) (X := G),
        (∀ g : PrimeRegularElement (G := G) p, d.val g.val = d'.val g.val) → d = d') :
    DefectZeroReductionSource iota := by
  exact {
    existsUniqueReduction := existsUnique_reduction_of_availability iota availability T
    regularRestriction_injective := hregular }

theorem reductions_agree_of_sources
    (iota : PrimeRegularRootEmbedding p k K G)
    (D D' : DefectZeroReductionSource iota)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G)) :
    D.reduce (iota := iota) d = D'.reduce (iota := iota) d :=
  congrArg (fun F : DefectZeroReductionSource iota => F.reduce (iota := iota) d)
    (Subsingleton.elim D D')

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalGlobalDefectZeroReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
