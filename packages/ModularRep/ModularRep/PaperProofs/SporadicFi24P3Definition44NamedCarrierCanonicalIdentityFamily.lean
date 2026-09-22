import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityPacket
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41

/-! One normalized correspondence gives all actual identity packets when
the group is centreless and every automorphism is inner. The representative
local reduction is derived from the existing selected quotient sources. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityFamily

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter TrivialWeightIdentification)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativePackets
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityPacket

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

theorem trivialWeightIdentification (T : TrivialWeightSource (p := p) (X := X)) :
    TrivialWeightIdentification (K := K) T := by
  refine ⟨?_⟩
  intro d d' h
  let Q : RadicalSubgroup (p := p) (G := X) := ⟨⊥, T.trivialRadical⟩
  let theta : LocalDefectZeroCharacter (K := K) Q :=
    ⟨(T.rawAtOne d).localCharacter, (T.rawAtOne d).defectZero⟩
  let theta' : LocalDefectZeroCharacter (K := K) Q :=
    ⟨(T.rawAtOne d').localCharacter, (T.rawAtOne d').defectZero⟩
  have ht : theta = theta' := by
    apply (localDefectZeroEquivWeightRadicalFibre (K := K) T.prime Q).injective
    apply Subtype.ext
    rw [localDefectZeroEquivWeightRadicalFibre_apply_val,
      localDefectZeroEquivWeightRadicalFibre_apply_val]
    exact h
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have heval := congrArg
    (fun t : LocalDefectZeroCharacter (K := K) Q =>
      t.1 (SporadicCompleteCollapseLemma52Actual.trivialNormalizerQuotientMk x)) ht
  exact (T.rawAtOne_localCharacter_mk d x).symm.trans
    (heval.trans (T.rawAtOne_localCharacter_mk d' x))

def ofNormalizedEquiv
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource p X) (hc : Subgroup.center X = ⊥)
    (allInner : ∀ a : MulAut X, ∃ x : X, a = MulAut.conj x)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Definition41Witness iota hinj R C Cover hc D T := by
  refine {
    Omega := Omega
    equivariant := hOmega
    block_preserving := hblock
    classQOne := hOne
    compatibility := compatibility
    packets := ?_ }
  intro Q xi
  let P := problemAt iota hinj R (canonicalSelectedReduction iota R C) xi.1
  let psi := ownBrauerAt iota hinj R (canonicalSelectedReduction iota R C) xi.1
  let V : CharacterWeight p K X := characterWeightAt iota.prime Q (localMap iota Omega iota.prime Q xi)
  have hclass : (Quotient.mk'' (Quotient.mk'' V) : WeightClass (p := p) (K := K) (X := X)) = Omega xi.1 :=
    localMap_class iota Omega iota.prime Q xi
  refine identityPacket P hc psi allInner Omega D T hOne V hclass
    (C V) compatibility fieldSource ?_
  change R.1.operations.rawWeightBlock V = operationsBlock iota hinj R xi.1
  exact (congrArg R.1.weightBlock hclass).trans (hblock xi.1)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
