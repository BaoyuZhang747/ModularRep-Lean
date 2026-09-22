import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerCanonicalRoot
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeRegularLifting
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel

/-! Recover the local quotient reduction from the actual canonical
normalizer character. Normal-p-subgroup kernels and regular-element lifting
are proved internally; the own quotient character, its reduction, and the
original normalizer pullback introduce no additional source principle. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientRawReduction

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.TypeBCentralKernelBrauerInflation
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeRegularLifting
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel

universe u

section Generic

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

def canonicalRawReductionOfNormalizer
    (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X)
    (phiN : IBr (normalizerRootAt iota W))
    (hReduction : NormalizerInflatedReduction W.subgroup W.localCharacter
      (normalizerRootAt iota W) phiN) : CanonicalRawReduction iota W := by
  let regular := primeRegularQuotientLiftPrinciple.{u} p
  let kernel := navarro232Principle p k
  let N := Subgroup.normalizer (W.subgroup : Set X)
  let R : Subgroup N := W.subgroup.subgroupOf N
  let hR : IsPGroup p R := W.radical.isPGroup.comap_subtype
  let q : N →* NormalizerQuotient W.subgroup := QuotientGroup.mk' R
  let E : IBr (localQuotientRoot iota W.subgroup) ≃ IBr (normalizerRootAt iota W) :=
    brauerEquiv R hR (localQuotientRoot iota W.subgroup) kernel regular
  let phiQ := E.symm phiN
  have hinflate : PrimeRegularClassFunction.pullback q phiQ.1 = phiN.1 := by
    calc
      PrimeRegularClassFunction.pullback q phiQ.1 = (E phiQ).1 :=
        (brauerEquiv_val R hR (localQuotientRoot iota W.subgroup) kernel regular phiQ).symm
      _ = phiN.1 := congrArg Subtype.val (E.apply_symm_apply phiN)
  refine { brauer := phiQ, reduction := ?_ }
  intro x
  obtain ⟨n, rfl⟩ := regular N R iota.prime hR x
  have hn := congrArg (fun chi : PrimeRegularClassFunction K N p => chi n) hinflate
  exact (hReduction n).trans hn.symm

theorem canonicalRawReductionOfNormalizer_localBrauer
    (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X)
    (phiN : IBr (normalizerRootAt iota W))
    (hReduction : NormalizerInflatedReduction W.subgroup W.localCharacter
      (normalizerRootAt iota W) phiN) :
    (canonicalRawReductionOfNormalizer iota W phiN hReduction).localBrauer.1 =
      phiN.1 := by
  apply PrimeRegularClassFunction.ext
  intro n
  exact ((canonicalRawReductionOfNormalizer iota W
    phiN hReduction).localBrauer_reduction n).symm.trans (hReduction n)

end Generic

open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerCanonicalRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H) (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))

local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩
local instance quotientFintype : Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _

variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi) (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)

def ownQuotientRawReduction :
    CanonicalRawReduction (quotientRoot P.iota (centralCharacterKernel P psi))
      (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers) :=
  canonicalRawReductionOfNormalizer (quotientRoot P.iota (centralCharacterKernel P psi))
    (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers)
    (ownCanonicalNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers)
    (ownCanonicalNormalizerBrauer_reduction P psi V source compatibility hrawBlock hprimeTo normalizers)

theorem ownQuotientRawReduction_localBrauer :
    (ownQuotientRawReduction P psi V source compatibility hrawBlock hprimeTo normalizers).localBrauer.1 =
        (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 := by
  apply PrimeRegularClassFunction.ext
  intro n
  exact ((ownQuotientRawReduction P psi V source compatibility hrawBlock hprimeTo normalizers).localBrauer_reduction n).symm.trans
      (ownNormalizerBrauer_reduction P psi V source compatibility hrawBlock hprimeTo normalizers n)

theorem ownQuotientRawReduction_pullback :
    PrimeRegularClassFunction.pullback (ownNormalizerMap P psi V)
      (ownQuotientRawReduction P psi V source compatibility hrawBlock hprimeTo normalizers).localBrauer.1 = source.localBrauer.1 := by
  rw [ownQuotientRawReduction_localBrauer]
  exact ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock hprimeTo normalizers

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientRawReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
