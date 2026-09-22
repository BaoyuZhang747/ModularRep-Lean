import ModularRep.BrauerCharacterHomPullback
import ModularRep.PaperProofs.EvenFieldFLZ318SelfCover

/-!
# Character-level extensions in the even-field cyclic endgame

`CyclicEndgameData` constructs extensions of representations.  The source
criterion is stated for Brauer characters.  This module closes the global
and quotient-level character gap in Lemma 2.10: after compatible prime regular
root lifts have been supplied from the chosen modular system, the ambient
extension representation affords an actual irreducible Brauer character
whose restriction is the prescribed global character or the prescribed local
character on the quotient.  Inflation of the latter character from the
quotient pair stabiliser to the pair stabiliser is treated separately.

The compatibility premises are eigenvalue-level equalities.  They are the
standard E1 consequence of choosing one global correspondence between
prime-to-`p` roots of unity in the modular system.  The declarations below
do not assert the existence of that correspondence, invoke
Feng--Li--Zhang, Theorem 3.18, or conclude BAW-goodness or iBAW.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZ318CharacterExtensions

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks field block)
variable (quotientInput : RawNormalizerQuotientInput
  (p := p) (K := K) (H := H))
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

/-- The representation extension supplied by the cyclic endgame gives an
actual ambient irreducible Brauer character extending the transported global
character.  Root compatibility is kept as a source-shaped E1 premise. -/
theorem globalBrauerCharacterExtension_of_cyclicEndgame
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction)
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks field block
        T.outerBlock_fixed T.brauerBlock_transport
    let haction := FibreTransportSource.brauerFibre_compatible
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) (T := T)
    let _ : MulAction (H ⋊[field] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction field haction
    let hinner : ∀ h : H,
        (SemidirectProduct.inl h : H ⋊[field] E) • psi = psi := fun h ↦ by
      rw [semidirect_inl_smul]
      exact FibreTransportSource.inner_fixes_brauerFibre
        (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
        (blockSource := blockSource) (block := block) (T := T) h psi
    let eH := canonicalHToEmbeddedEquiv psi hinner
    let iotaEmbedded := iota.alongMulEquiv eH
    ∀ (iotaAmbient : PrimeRegularRootEmbedding p k K
        (semidirectStabilizer (phi := field) psi)),
      (∀ (W : FDRep k (embeddedHStabilizer (phi := field) psi))
        (extension : Representation.Extension
          (embeddedHStabilizer (phi := field) psi) W.ρ),
        Representation.BrauerRootLiftCompatibleAlong
          extension.representation iotaAmbient iotaEmbedded
          (embeddedHStabilizer (phi := field) psi).subtype) →
      ∃ psiEmbedded : IBr iotaEmbedded,
        psiEmbedded.1 = pullbackPrimeRegularAlongEquiv eH psi.1.1 ∧
        Nonempty
          (Representation.Extension.BrauerCharacterExtensionWitness
            iotaAmbient iotaEmbedded psiEmbedded) := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (FibreTransportSource.innerBlock_fixed
        (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  letI : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport
  let haction := FibreTransportSource.brauerFibre_compatible
    (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
    (blockSource := blockSource) (block := block) (T := T)
  letI : MulAction (H ⋊[field] E)
      (BrauerFibre iota hinj blocks block) :=
    semidirectMulAction field haction
  have hinner : ∀ h : H,
      (SemidirectProduct.inl h : H ⋊[field] E) • psi = psi := by
    intro h
    rw [semidirect_inl_smul]
    exact FibreTransportSource.inner_fixes_brauerFibre
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) (T := T) h psi
  let eH := canonicalHToEmbeddedEquiv psi hinner
  let iotaEmbedded := iota.alongMulEquiv eH
  intro iotaAmbient rootCompatible
  rcases endgame.global_extension psi with
    ⟨W, hW, hcharacter, ⟨extension⟩⟩
  let psiEmbedded : IBr iotaEmbedded :=
    ⟨pullbackPrimeRegularAlongEquiv eH psi.1.1,
      ⟨W, hW, hcharacter⟩⟩
  refine ⟨psiEmbedded, rfl, ⟨?_⟩⟩
  exact Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
    extension hW iotaAmbient iotaEmbedded psiEmbedded hcharacter.symm
      (rootCompatible W extension)

/-- The quotient-level local representation extension supplied by the
cyclic endgame affords an actual irreducible Brauer character of the
quotient pair stabiliser extending the selected defect-zero reduction. -/
theorem localBrauerCharacterExtension_of_cyclicEndgame
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction)
    (psi : BrauerFibre iota hinj blocks block) :
    let w := endgame.omega.toEquiv psi
    letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        quotientInput w
    ∀ (iotaAmbient : PrimeRegularRootEmbedding p k K
        (PairStabilizer field blockSource block w ⧸
          EmbeddedRadical field blockSource block quotientInput w)),
      (∀ (W : FDRep k (LocalBase field blockSource block quotientInput w))
        (extension : Representation.Extension
          (LocalBase field blockSource block quotientInput w) W.ρ),
        Representation.BrauerRootLiftCompatibleAlong
          extension.representation iotaAmbient
          (transportedLocalRootEmbedding
            field blockSource block quotientInput w (localReduction w))
          (LocalBase field blockSource block quotientInput w).subtype) →
      Nonempty
        (Representation.Extension.BrauerCharacterExtensionWitness
          iotaAmbient
          (transportedLocalRootEmbedding
            field blockSource block quotientInput w (localReduction w))
          (transportedLocalBrauer
            field blockSource block quotientInput w (localReduction w))) := by
  dsimp only
  let w := endgame.omega.toEquiv psi
  letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := field) (blockSource := blockSource) (block := block)
      quotientInput w
  intro iotaAmbient rootCompatible
  rcases endgame.local_extension psi with
    ⟨W, hW, hcharacter, _hreduction, ⟨extension⟩⟩
  exact ⟨Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
    extension hW iotaAmbient
      (transportedLocalRootEmbedding
        field blockSource block quotientInput w (localReduction w))
      (transportedLocalBrauer
        field blockSource block quotientInput w (localReduction w))
      hcharacter.symm (rootCompatible W extension)⟩

end ModularRep.PaperProofs.EvenFieldFLZ318CharacterExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
