import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData
import ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual

/-! Every packet is constructed from one normalized correspondence and
the unselected lower quotient data. The cover supplies perfectness and
the full-centre order; all-inner action gives equivariance. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativePackets
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityPacket

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)

abbrev QuotientDataFamily (Cover : EllPrimeCoverSource p X) :=
  ∀ (phi : IBr iota) (V : CharacterWeight p K X),
    OriginalQuotientData
      (problemAt iota hinj R (canonicalSelectedReduction iota R C) phi)
      (ownBrauerAt iota hinj R (canonicalSelectedReduction iota R C) phi)
      V Cover.centerPrimeTo

theorem equivariant_of_allInner
    (allInner : SporadicCompleteCollapseLemma52Actual.AllAutomorphismsInner (X := X))
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X)) :
    ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi := by
  intro a phi
  obtain ⟨x, hx⟩ := allInner.eq_conj a.unop
  have hphi : a • phi = phi := by
    apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    rw [hx]
    exact PrimeRegularClassFunction.twist_conj phi.1 x
  have ha : a = MulOpposite.op (MulAut.conj x) := by
    apply MulOpposite.unop_injective
    exact hx
  have hw : ∀ w : WeightClass (p := p) (K := K) (X := X), a • w = w := by
    intro w
    rw [ha]
    refine Quotient.inductionOn w ?_
    intro W
    apply Quotient.sound
    refine ⟨x⁻¹, ?_⟩
    change CharacterWeight.rightTwistIsoClass (MulAut.conj (x⁻¹)⁻¹) W =
      CharacterWeight.rightTwistIsoClass (MulAut.conj x) W
    simp
  rw [hphi, hw]

def ofNormalizedEquiv
    (Cover : EllPrimeCoverSource p X)
    (allInner : SporadicCompleteCollapseLemma52Actual.AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C Cover)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Definition41Witness iota hinj R C Cover D T := by
  refine {
    Omega := Omega
    equivariant := equivariant_of_allInner iota allInner Omega
    block_preserving := hblock
    classQOne := hOne
    compatibility := compatibility
    packets := ?_ }
  intro Q xi
  let P := problemAt iota hinj R (canonicalSelectedReduction iota R C) xi.1
  letI : Group.IsPerfect P.H := ⟨Cover.perfect⟩
  let psi := ownBrauerAt iota hinj R (canonicalSelectedReduction iota R C) xi.1
  let V := characterWeightAt iota.prime Q (localMap iota Omega iota.prime Q xi)
  let S := lower xi.1 V
  let := S.fintypeGlobalBlock
  let := S.fintypeLocalBlock
  have hclass : (Quotient.mk'' (Quotient.mk'' V) : WeightClass (p := p) (K := K) (X := X)) = Omega xi.1 :=
    localMap_class iota Omega iota.prime Q xi
  have hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks psi.1 := by
    change R.1.operations.rawWeightBlock V = operationsBlock iota hinj R xi.1
    exact (congrArg R.1.weightBlock hclass).trans (hblock xi.1)
  exact identityOriginalPacket P psi V (C V) compatibility hrawBlock
    Cover.centerPrimeTo S.normalizers S.globalBlocks S.localBlocks
    S.globalCatalogue S.localCatalogue S.intervalLaw S.globalImageLaw S.localImageLaw
    allInner.eq_conj Omega D T hOne hclass fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
