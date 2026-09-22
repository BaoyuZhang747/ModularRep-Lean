import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence

/-! The own normalizer descent restricts the original root table. It agrees
with the quotient ambient's canonical normalizer convention, so its actual
Brauer character and reduction need no additional root-agreement input. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerCanonicalRoot

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

universe u

local instance quotientFintype (P : Definition35Problem.{u}) (psi : Definition35Brauer P) :
    Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _

private theorem root_eq_of_table_eq
    {p : ℕ} {k K G : Type*} [Field k] [Field K] [Group G] [Finite G]
    (i j : PrimeRegularRootEmbedding p k K G)
    (h : i.toMulEquiv = j.toMulEquiv) : i = j := by
  cases i
  cases j
  cases h
  rfl

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

variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi) (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)

theorem ownNormalizerRoot_eq_canonical :
    ownNormalizerRoot P psi V source hprimeTo normalizers =
      normalizerRootAt (quotientRoot P.iota (centralCharacterKernel P psi))
        (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers) := by
  unfold ownNormalizerRoot
  rw [source.normalizerRoot_eq, normalizerRootAt_eq_subgroupRoot,
    normalizerRootAt_eq_subgroupRoot]
  apply root_eq_of_table_eq
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  rfl

def ownCanonicalNormalizerBrauer :
    IBr (normalizerRootAt (quotientRoot P.iota (centralCharacterKernel P psi))
      (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers)) :=
  ⟨(ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1, by
    rw [← ownNormalizerRoot_eq_canonical P psi V source compatibility hrawBlock hprimeTo normalizers]
    exact (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).2⟩

theorem ownCanonicalNormalizerBrauer_val :
    (ownCanonicalNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 =
      (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 := rfl

theorem ownCanonicalNormalizerBrauer_reduction :
    NormalizerInflatedReduction
      (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers).subgroup
      (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers).localCharacter
      (normalizerRootAt (quotientRoot P.iota (centralCharacterKernel P psi))
        (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers))
      (ownCanonicalNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers) := by
  intro n
  exact ownNormalizerBrauer_reduction P psi V source compatibility hrawBlock hprimeTo normalizers n

theorem ownCanonicalNormalizerBrauer_pullback :
    PrimeRegularClassFunction.pullback (ownNormalizerMap P psi V)
      (ownCanonicalNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 =
        source.localBrauer.1 :=
  ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock hprimeTo normalizers

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerCanonicalRoot


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
