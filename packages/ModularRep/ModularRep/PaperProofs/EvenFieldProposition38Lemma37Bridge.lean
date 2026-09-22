import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
import ModularRep.PaperProofs.CyclicOuterLocalRepresentationInflation
import ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual

/-!
# The even-field Proposition 3.8--Lemma 2.10 bridge

This module connects the literal block-fibre equivalence constructed in
Proposition 3.8 with the semidirect equivariance and cyclic-extension
deductions already checked for Lemma 2.10.  It does not assert BAW-goodness or
iBAW.

The remaining inputs are classified as follows.

* E1: automorphism transport of the Brauer block label, the cyclic
  Brauer-extension principle, and defect-zero reduction.
* K: the normaliser quotient formula is constructed canonically from subgroup
  conjugation; it is not an application-supplied premise.
* E2: the cited representation theoretic inputs already exposed by the
  concrete Lemmas 3.6--3.7 and Proposition 3.8 endpoints, and
  Feng--Li--Zhang, Theorem 3.18 itself.
* U: instantiation of those E1 and E2 interfaces on the manuscript block,
  including the local root embeddings and reductions.  The selected block's
  field stability is retained exactly as the stated hypothesis of Lemma 2.10.
* L: the final invocation of Feng--Li--Zhang, Theorem 3.18, and packaging of
  its conclusion.  The remaining exact hypotheses of that theorem are kept
  outside this endpoint; depending on the clause, their evidence is E1, K,
  or U.

No character fixedness statement or extension is supplied.  The outer
equivariance and bijection come from the Proposition 3.8 equivalence.  Lean
derives full semidirect equivariance and both the global and matched local
extensions.
-/

namespace ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

open scoped MonoidAlgebra

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldEJGCPairActual
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters
open ModularRep.OrdinaryIrreducibleCharacter

noncomputable section

/-- The opposite-field action used in Proposition 3.8 is the manuscript right
action of the inverse field automorphism used in Lemma 2.10. -/
theorem inverseOpHom_fieldAction_eq
    (r a : ℕ) (ha : 0 < a) (e : FieldGroup a) :
    inverseOpHom (fieldAction r a ha) e =
      oppositeFieldAction r a ha (MulOpposite.op e⁻¹) := by
  rfl

universe u

section CyclicEndgame

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (phi : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks phi block)

/-- The exact global extension conclusion proved by the literal-fibre
endpoint for Lemma 2.10. -/
abbrev GlobalExtensionConclusion
    (psi : BrauerFibre iota hinj blocks block) : Prop :=
  let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (FibreTransportSource.innerBlock_fixed
        (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport
  let hcompat := FibreTransportSource.brauerFibre_compatible
    (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
    (blockSource := blockSource) (block := block) (T := T)
  let _ : MulAction (H ⋊[phi] E) (BrauerFibre iota hinj blocks block) :=
    semidirectMulAction phi hcompat
  let hinner : ∀ h : H,
      (SemidirectProduct.inl h : H ⋊[phi] E) • psi = psi := fun h ↦ by
    rw [semidirect_inl_smul]
    exact FibreTransportSource.inner_fixes_brauerFibre
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) (T := T) h psi
  let eH := canonicalHToEmbeddedEquiv psi hinner
  let iotaEmbedded := iota.alongMulEquiv eH
  ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
    Representation.IsIrreducible W.ρ ∧
    pullbackPrimeRegularAlongEquiv eH psi.1.1 =
      Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
    Nonempty (Representation.Extension
      (embeddedHStabilizer (phi := phi) psi) W.ρ)

/-- The part of the Proposition 3.8--Lemma 2.10 endgame that is derived in the
kernel before the remaining Feng--Li--Zhang criterion clauses are invoked. -/
structure CyclicEndgameData
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w) where
  omega : EquivariantEquiv E
    (BrauerFibre iota hinj blocks block)
    (WeightFibre blockSource block)
    (rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport).smul
    (rightWeightFibreMulAction phi blockSource block
      T.outerBlock_fixed).smul
  semidirect_equivariant :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    let _ : MulAction (H ⋊[phi] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi
        (FibreTransportSource.brauerFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
          (blockSource := blockSource) (block := block) (T := T))
    let _ : MulAction (H ⋊[phi] E) (WeightFibre blockSource block) :=
      semidirectMulAction phi
        (FibreTransportSource.weightFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
          (blockSource := blockSource) (block := block) (T := T))
    ∀ (g : H ⋊[phi] E) (psi : BrauerFibre iota hinj blocks block),
      omega.toEquiv (g • psi) = g • omega.toEquiv psi
  global_extension : ∀ psi : BrauerFibre iota hinj blocks block,
    GlobalExtensionConclusion
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T psi
  local_extension : ∀ psi : BrauerFibre iota hinj blocks block,
    LocalExtensionConclusion (phi := phi) (blockSource := blockSource)
      (block := block) quotientInput
      (omega.toEquiv psi) (localReduction (omega.toEquiv psi))

/-- An outer-equivariant equivalence on the literal block fibres determines
the full semidirect equivariance and both cyclic extensions.  Fixedness and
extension are conclusions, not fields of the input equivalence. -/
noncomputable def cyclicEndgameDataOfEquivariantEquiv
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w)
    (omega : EquivariantEquiv E
      (BrauerFibre iota hinj blocks block)
      (WeightFibre blockSource block)
      (rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport).smul
      (rightWeightFibreMulAction phi blockSource block
        T.outerBlock_fixed).smul) :
    CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction where
  omega := omega
  semidirect_equivariant :=
    FibreTransportSource.fibreMap_semidirect_equivariant
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) (T := T)
      omega.toEquiv omega.equivariant
  global_extension := fun psi ↦
    FibreTransportSource.global_extension_brauerFibre_actual
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) (T := T) principle psi
  local_extension := fun psi ↦
    selectedLiteralLocalExtension
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput principle (omega.toEquiv psi)
      (localReduction (omega.toEquiv psi))

end CyclicEndgame

section FieldOrientation

variable {K k ι : Type}
variable [Field K] [Field k] [CharZero K]
variable {r a ell : ℕ} (ha : 0 < a)
variable [CharP k ell] [IsAlgClosed k]
variable [Fintype (FiniteSymplecticFixed r a)] [Fintype ι]
variable {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
variable (iota : PrimeRegularRootEmbedding ell k K
  (FiniteSymplecticFixed r a))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
variable (blockSource : LocalBlockInductionSource
  (p := ell) (k := k) (K := K)
  (G := FiniteSymplecticFixed r a) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks
  (fieldAction r a ha) block)

include T

/-- Field stability for the opposite action is derived from stability for the
manuscript right field action. -/
theorem oppositeFieldBlock_fixed_of_fibreTransport
    (sigma : (FieldGroup a)ᵐᵒᵖ) :
    oppositeFieldAction r a ha sigma • block = block := by
  have h := T.outerBlock_fixed (MulOpposite.unop sigma)⁻¹
  rw [inverseOpHom_fieldAction_eq] at h
  simpa using h

/-- The narrow Proposition 3.8 block-transport source is the restriction of
the full automorphism-transport source already required by Lemma 2.10. -/
theorem actualBijectionSourceOfFibreTransport :
    ActualBijectionSource r a ell ha iota hinj blocks where
  brauerBlock_transport := fun sigma psi ↦
    T.brauerBlock_transport (oppositeFieldAction r a ha sigma) psi

/-- Reindex an opposite-field equivariant equivalence by inversion to obtain
the manuscript right-field equivariant equivalence. -/
def rightEquivariantEquivOfOpposite
    (omega : EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (BrauerFibre iota hinj blocks block)
      (WeightFibre blockSource block)
      (automorphismIBrBlockMulAction (oppositeFieldAction r a ha)
        ((actualBijectionSourceOfFibreTransport
            (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
            (block := block) (T := T)).isAutomorphismStableIBrBlock
          ha iota hinj blocks block
          (oppositeFieldBlock_fixed_of_fibreTransport
            (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
            (block := block) (T := T)))).smul
      (oppositeFieldWeightFibreMulAction
        (r := r) (a := a) ha blockSource block
        (oppositeFieldBlock_fixed_of_fibreTransport
          (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
          (block := block) (T := T))).smul) :
    EquivariantEquiv (FieldGroup a)
      (BrauerFibre iota hinj blocks block)
      (WeightFibre blockSource block)
      (rightIBrBlockMulAction iota hinj blocks
        (fieldAction r a ha) block
        T.outerBlock_fixed T.brauerBlock_transport).smul
      (rightWeightFibreMulAction (fieldAction r a ha) blockSource block
        T.outerBlock_fixed).smul where
  toEquiv := omega.toEquiv
  equivariant e psi := by
    have hop := omega.equivariant (MulOpposite.op e⁻¹) psi
    have hsource :
        (rightIBrBlockMulAction iota hinj blocks
          (fieldAction r a ha) block
          T.outerBlock_fixed T.brauerBlock_transport).smul e psi =
        (automorphismIBrBlockMulAction (oppositeFieldAction r a ha)
          ((actualBijectionSourceOfFibreTransport
              (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
              (block := block) (T := T)).isAutomorphismStableIBrBlock
            ha iota hinj blocks block
            (oppositeFieldBlock_fixed_of_fibreTransport
              (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
              (block := block) (T := T)))).smul
          (MulOpposite.op e⁻¹) psi := by
      apply Subtype.ext
      change inverseOpHom (fieldAction r a ha) e • psi.1 =
        oppositeFieldAction r a ha (MulOpposite.op e⁻¹) • psi.1
      rw [inverseOpHom_fieldAction_eq]
    have htarget :
        (rightWeightFibreMulAction (fieldAction r a ha) blockSource block
          T.outerBlock_fixed).smul e (omega.toEquiv psi) =
        (oppositeFieldWeightFibreMulAction
          (r := r) (a := a) ha blockSource block
          (oppositeFieldBlock_fixed_of_fibreTransport
            (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
            (block := block) (T := T))).smul
          (MulOpposite.op e⁻¹) (omega.toEquiv psi) := by
      apply Subtype.ext
      change inverseOpHom (fieldAction r a ha) e • (omega.toEquiv psi).1 =
        oppositeFieldAction r a ha (MulOpposite.op e⁻¹) •
          (omega.toEquiv psi).1
      rw [inverseOpHom_fieldAction_eq]
    rw [hsource, hop, ← htarget]

end FieldOrientation

section ActualEndpoint

/-- The actual-carrier Proposition 3.8 equivalence, reindexed to the manuscript
right field action, supplies all K-level conclusions of the cyclic-outer
argument.  The theorem stops before every remaining clause of the cited
criterion. -/
theorem proposition_3_8_to_lemma_3_7_actual
    {A Dual CitedRelativeWeylGroup K O k ι : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [CharZero K]
    (r a ell : ℕ) (ha : 0 < a) [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)ᵐᵒᵖ] [IsCyclic (FieldGroup a)ᵐᵒᵖ]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (block : ι)
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    (initial : pairs.RestrictedPair block)
    (GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a)))
    [Fintype (W D coherence block)]
    [Fintype (pairs.DefectZeroUnion block)]
    (cited :
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.CitedData
        (CitedRelativeWeylGroup := CitedRelativeWeylGroup) ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
        D coherence block pairs initial GeneralisedSeries)
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment D pairs blockIdempotent blockSource)
    (T : FibreTransportSource iota hinj blocks
      (fieldAction r a ha) block)
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (basicSet : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
        (decompositionMapOfStableReduction Msys iota hcompat))
    [Finite (↑(XC ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))]
    (fmz62 :
      let hfixed := oppositeFieldBlock_fixed_of_fibreTransport
        (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
        (block := block) (T := T)
      FMZ62TypeCRestrictedApplication
        r a ell ha D coherence block S35 pairs blockSource alignment hfixed)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{0, 0}
      (p := 2) (A := (FieldGroup a)ᵐᵒᵖ))
    (burnside : PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{0, 0}
      (A := (FieldGroup a)ᵐᵒᵖ))
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w) :
    let fixation :=
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
        r a ell ha D coherence block S35
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
      characterOppositeMulAction fixation
    ∀ _hordinary : OrdinaryTwistCompatibleLabels basicSet
        (oppositeFieldAction r a ha),
      Nonempty (CyclicEndgameData
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (phi := fieldAction r a ha) (blockSource := blockSource)
        (block := block) T
        (canonicalRawNormalizerQuotientInput
          (p := ell) (K := K) (H := FiniteSymplecticFixed r a))
        localReduction) := by
  dsimp only
  intro _hordinary
  let source : ActualBijectionSource r a ell ha iota hinj blocks :=
    actualBijectionSourceOfFibreTransport
      (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
      (block := block) (T := T)
  let hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block :=
    oppositeFieldBlock_fixed_of_fibreTransport
      (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
      (block := block) (T := T)
  obtain ⟨omegaOpp⟩ := proposition_3_8_equivariant_bijection_actual
    r a ell ha block D coherence S35 pairs initial GeneralisedSeries cited
    iota hinj blocks blockSource alignment source hfixed Msys hcompat
    basicSet fmz62
    conlon burnside _hordinary
  let omega := rightEquivariantEquivOfOpposite
    (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
    (blockSource := blockSource) (block := block) (T := T) omegaOpp
  let quotientInput := canonicalRawNormalizerQuotientInput
    (p := ell) (K := K) (H := FiniteSymplecticFixed r a)
  exact ⟨cyclicEndgameDataOfEquivariantEquiv
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (phi := fieldAction r a ha) (blockSource := blockSource)
    (block := block) (T := T) principle quotientInput localReduction omega⟩

end ActualEndpoint

end

end ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
