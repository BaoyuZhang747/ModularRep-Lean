import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer

/-! Global and local base invariance on the constructed original ambient.
Perfectness, the central kernel and the full automorphism equivalence are
derived from the original universal cover and trivial central sector. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCentralSector
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient

universe u

theorem actualGlobalBaseFixed
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [Group G] [Finite G]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
    (hcenter : Subgroup.center G = ⊥) (a : ActualAutAmbient iota phi) :
    IrreducibleBrauerCharacter.twist
        (iota.alongMulEquiv (actualBaseEquiv iota phi hcenter))
        (IrreducibleBrauerCharacter.alongMulEquiv iota
          (actualBaseEquiv iota phi hcenter) phi) (MulAut.conjNormal a) =
      IrreducibleBrauerCharacter.alongMulEquiv iota (actualBaseEquiv iota phi hcenter) phi := by
  let e := actualBaseEquiv iota phi hcenter
  let beta := actualConjugation iota phi a
  have he : MulAut.congr e beta = MulAut.conjNormal a := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    change e (beta (e.symm (e x))) = MulAut.conjNormal a (e x)
    rw [e.symm_apply_apply]
    apply Subtype.ext
    exact innerEmbedding_conjugation iota phi a x
  have hf : phi.1.twist beta = phi.1 :=
    congrArg Subtype.val (actualConjugation_brauer_fixed iota phi a)
  apply Subtype.ext
  change (PrimeRegularClassFunction.equivAlongMulEquiv e phi.1).twist (MulAut.conjNormal a) =
    PrimeRegularClassFunction.equivAlongMulEquiv e phi.1
  have ht := PrimeRegularClassFunction.equivAlongMulEquiv_twist e phi.1 beta
  rw [hf, he] at ht
  exact ht.symm

section Original

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable {S : Type u} [Group S] (q : P.H →* S)
variable (hq : IsUniversalCentralExtension q)
variable (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
variable (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
  psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
    psi.1.1 ⟨1, isPrimeRegular_one⟩)

theorem originalGlobalBaseFixed :
    let B := trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal
    let rG := quotientRoot P.iota (centralCharacterKernel P psi)
    ∀ a : B.A, IrreducibleBrauerCharacter.twist (rG.alongMulEquiv B.baseEquiv)
        (IrreducibleBrauerCharacter.alongMulEquiv rG B.baseEquiv (ownQuotientBrauer P psi))
        (MulAut.conjNormal a) =
      IrreducibleBrauerCharacter.alongMulEquiv rG B.baseEquiv (ownQuotientBrauer P psi) := by
  let : Group.IsPerfect P.H := ⟨perfect_of_universalCentralExtension q hq⟩
  dsimp only
  intro a
  exact actualGlobalBaseFixed _ (ownQuotientBrauer P psi)
    (ownQuotient_center_eq_bot P psi
      (centralCharacterKernel_eq_center_of_trivial_sector P psi hcenter hglobal)) a

variable (V : CharacterWeight P.p P.K P.H)
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
theorem originalLocalBaseFixed :
    let C := actualLocalNormalizerData P psi V q hq hs hna hcenter hglobal
    let rN := ownNormalizerRoot P psi V source hprimeTo normalizers
    let phiN := ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers
    ∀ d : C.D, IrreducibleBrauerCharacter.twist (rN.alongMulEquiv C.eM)
        (IrreducibleBrauerCharacter.alongMulEquiv rN C.eM phiN) (MulAut.conjNormal d) =
      IrreducibleBrauerCharacter.alongMulEquiv rN C.eM phiN := by
  let : Group.IsPerfect P.H := ⟨perfect_of_universalCentralExtension q hq⟩
  dsimp only
  intro d
  exact own_actualLocalBrauer_fixed P psi V hprimeTo normalizers source compatibility hrawBlock
    (centralCharacterKernel_eq_center_of_trivial_sector P psi hcenter hglobal) hcenter
    (trivialSectorAutEquiv P psi q hq hs hna hcenter hglobal)
    (trivialSectorAutEquiv_square P psi q hq hs hna hcenter hglobal) Omega hOmega hclass d

end Original

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
