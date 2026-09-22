import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence

/-! The trivial-weight block identity at the root table restricted from the
original group. The arbitrary-root compatibility law is not used. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialBlock
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence

universe u

theorem trivialWeightBlockCompatibilityOfCanonicalOperations
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    TrivialWeightBlockCompatibility iota hinj R.1.operations.ambientBlockData.blocks R D T := by
  classical
  let O := R.1.operations
  let := O.ambientBlockData.fintypeBlock
  refine ⟨?_⟩
  intro d
  let W := T.rawAtOne d
  let N : Subgroup X := Subgroup.normalizer ((⊥ : Subgroup X) : Set X)
  let : Fintype N := Fintype.ofFinite _
  let : Fintype (Subgroup.normalizer (W.subgroup : Set X)) := Fintype.ofFinite _
  let localData := O.inflatedNormalizerBlockData W.subgroup
  let := localData.fintypeBlock
  let e : N ≃* X := trivialNormalizerEquiv
  have he : e.toMonoidHom = N.subtype := by
    ext n
    rfl
  let phi := D.reduce (iota := iota) d
  let s := C W
  let rootN := s.normalizerRoot
  let phiN := s.localBrauer
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rootN
  have hroot : rootN = iota.alongMulEquiv e.symm := by
    change s.normalizerRoot = iota.alongMulEquiv e.symm
    rw [s.normalizerRoot_eq, normalizerRootAt_eq_subgroupRoot]
    change subgroupRoot iota N = iota.alongMulEquiv e.symm
    have hN : primeRegularExponent p N ∣ primeRegularExponent p X := by
      simpa only [primeRegularExponent] using
        Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card N) p
    simpa only [commonRoot_self, subgroupRoot] using
      (ofCommonRoot_alongMulEquiv iota.prime iota.toMulEquiv (dvd_refl _) hN e.symm).symm
  have hlift : rootN.lift = iota.lift := by
    rw [hroot]
    change (iota.alongMulEquiv e.symm).lift = iota.lift
    funext z
    exact PrimeRegularRootEmbedding.alongMulEquiv_lift iota e.symm z
  have hphi : phiN.1 = PrimeRegularClassFunction.pullback e.toMonoidHom phi.1 := by
    apply PrimeRegularClassFunction.ext
    intro n
    calc
      phiN.1 n = W.localCharacter (QuotientGroup.mk n.1) := (s.localBrauer_reduction n).symm
      _ = phi.1 (PrimeRegularElement.map e.toMonoidHom n) := by
        change d.1 n.1.1 = phi.1 (PrimeRegularElement.map e.toMonoidHom n)
        exact D.reduce_isReduction (iota := iota) d (PrimeRegularElement.map e.toMonoidHom n)
  let bG := irreducibleBrauerCharacterBlock iota hinj O.ambientBlockData.blocks phi
  let bL := O.inflateToNormalizer W.subgroup (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  have hLocal : irreducibleBrauerCharacterBlock rootN injN localData.blocks phiN = bL :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer W s
  have hTransported : irreducibleBrauerCharacterBlock rootN injN
      (O.ambientBlockData.blocks.alongMulEquiv e.symm) phiN = bG :=
    irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
      iota hinj rootN injN e.symm O.ambientBlockData.blocks phi phiN hlift hphi
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
  have hInduced : bG = O.induceToAmbient W :=
    eq_inducedBlock_of_blockInducesTo N localData.catalogue O.ambientBlockData.catalogue bL
      (O.blockInductionDefined W) hActual
  calc
    R.1.weightBlock (T.atOne d) = O.induceToAmbient W := rfl
    _ = bG := hInduced.symm
    _ = operationsBlock iota hinj R phi := rfl
    _ = _ := operationsBlock_eq iota hinj R O.ambientBlockData.blocks phi

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
