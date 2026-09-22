import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-! Individual extensions on the actual original-cover ambient are
constructed from one ambient root seed and the cyclic-extension theorem.
Both root agreements and exact restrictions are retained. A common Q=1
choice and specified block compatibility are separate subsequent deductions. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorIndividualExtensions

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open Representation.Extension
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H)
variable {S : Type u} [Group S] (q : P.H →* S)
variable (hq : IsUniversalCentralExtension q)
variable (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
variable (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
  psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
    psi.1.1 ⟨1, isPrimeRegular_one⟩)
variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))
local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩
variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi)
  (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)
variable (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
variable (hOmega : ∀ (a : (MulAut P.H)ᵐᵒᵖ) (chi : IBr P.iota),
  Omega (a • chi) = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)

include Omega hOmega hclass in
theorem exists_actualIndividualExtensions
    (hOuter : Nat.card (LiteralOuterQuotient (CentralCharacterQuotient P psi)) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K
      (trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal).A) :
    let B := trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal
    let C := actualLocalNormalizerData P psi V q hq hs hna hcenter hglobal
    let rG := quotientRoot P.iota (centralCharacterKernel P psi)
    let rN := ownNormalizerRoot P psi V source hprimeTo normalizers
    let phiN := ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers
    let rB := rG.alongMulEquiv B.baseEquiv
    let rM := rN.alongMulEquiv C.eM
    let phiB := IrreducibleBrauerCharacter.alongMulEquiv rG B.baseEquiv (ownQuotientBrauer P psi)
    let phiM := IrreducibleBrauerCharacter.alongMulEquiv rN C.eM phiN
    ∃ (rA : PrimeRegularRootEmbedding P.p P.k P.K B.A)
      (rD : PrimeRegularRootEmbedding P.p P.k P.K C.D),
      (∀ zeta : rootsOfUnity (primeRegularExponent P.p B.base) P.k,
        rB.lift (((zeta : P.kˣ) : P.k)) = rA.lift (((zeta : P.kˣ) : P.k))) ∧
      (∀ zeta : rootsOfUnity (primeRegularExponent P.p (B.base.comap C.D.subtype)) P.k,
        rM.lift (((zeta : P.kˣ) : P.k)) = rD.lift (((zeta : P.kˣ) : P.k))) ∧
      Nonempty (BrauerCharacterExtensionWitness rA rB phiB) ∧
      Nonempty (BrauerCharacterExtensionWitness rD rM phiM) := by
  let B := trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal
  let C := actualLocalNormalizerData P psi V q hq hs hna hcenter hglobal
  let rG := quotientRoot P.iota (centralCharacterKernel P psi)
  let rN := ownNormalizerRoot P psi V source hprimeTo normalizers
  let phiN := ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers
  let rB := rG.alongMulEquiv B.baseEquiv
  let rM := rN.alongMulEquiv C.eM
  let phiB := IrreducibleBrauerCharacter.alongMulEquiv rG B.baseEquiv (ownQuotientBrauer P psi)
  let phiM := IrreducibleBrauerCharacter.alongMulEquiv rN C.eM phiN
  have hcyclic : IsCyclic (B.A ⧸ B.base) :=
    actual_quotient_isCyclic rG (ownQuotientBrauer P psi) hOuter
  have hfixedGlobal : ∀ a : B.A,
      IrreducibleBrauerCharacter.twist rB phiB (MulAut.conjNormal a) = phiB :=
    originalGlobalBaseFixed P psi q hq hs hna hcenter hglobal
  have hfixedLocal : ∀ d : C.D,
      IrreducibleBrauerCharacter.twist rM phiM (MulAut.conjNormal d) = phiM :=
    originalLocalBaseFixed P psi q hq hs hna hcenter hglobal V hprimeTo normalizers
      source compatibility hrawBlock Omega hOmega hclass
  obtain ⟨rA, hA, hExtA⟩ := exists_extensionWitness_with_retained_agreement
    B.base principle rB phiB hcyclic hfixedGlobal seed
  obtain ⟨rD, hD, hExtD⟩ := exists_extensionWitness_with_retained_agreement
    (B.base.comap C.D.subtype) principle rM phiM
    (local_quotient_isCyclic B.base C.D hcyclic) hfixedLocal (seedOnSubgroup seed C.D)
  exact ⟨rA, rD, hA, hD, hExtA, hExtD⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorIndividualExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
