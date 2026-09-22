import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralNormalizer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight
import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent

/-! The actual quotient-normalizer Brauer character and its reduction from
the same constructed quotient weight. Roots, character, kernel triviality,
pullback and reduction are derived; no extra character source is used. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnLocalKernel
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

universe u
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

def ownNormalizerMap :
    Subgroup.normalizer (V.subgroup : Set P.H) →*
      Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
        Set (CentralCharacterQuotient P psi)) :=
  normalizerMap (centralCharacterQuotientMap P psi) V.subgroup

include hprimeTo normalizers in
theorem ownNormalizerMap_surjective : Function.Surjective (ownNormalizerMap P psi V) :=
  centralQuotientNormalizerMap_surjective (centralCharacterKernel P psi)
    inf_le_left hprimeTo V.subgroup V.radical normalizers

def ownNormalizerRoot :
    PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
        Set (CentralCharacterQuotient P psi))) :=
  surjectiveRoot source.normalizerRoot (ownNormalizerMap P psi V)
    (ownNormalizerMap_surjective P psi V hprimeTo normalizers)

def ownNormalizerKernelTrivial :
    KernelTrivialIBrAlong (ownNormalizerMap P psi V) source.normalizerRoot := by
  refine ⟨source.localBrauer,
    chosenIBrRepresentation source.normalizerRoot source.localBrauer,
    (Classical.choose_spec source.localBrauer.2).1,
    chosenIBrRepresentation_character source.normalizerRoot source.localBrauer, ?_⟩
  rw [ownNormalizerMap, centralNormalizerMap_ker]
  exact own_local_kernel P psi V source compatibility hrawBlock hprimeTo

def ownNormalizerBrauer :
    IBr (ownNormalizerRoot P psi V source hprimeTo normalizers) :=
  descendIBrAlong (ownNormalizerMap P psi V)
    (ownNormalizerMap_surjective P psi V hprimeTo normalizers)
    source.normalizerRoot (ownNormalizerRoot P psi V source hprimeTo normalizers)
    (ownNormalizerKernelTrivial P psi V source compatibility hrawBlock hprimeTo)

theorem ownNormalizerBrauer_pullback :
    PrimeRegularClassFunction.pullback (ownNormalizerMap P psi V)
      (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 =
        source.localBrauer.1 :=
  descendIBrAlong_pullback (ownNormalizerMap P psi V)
    (ownNormalizerMap_surjective P psi V hprimeTo normalizers)
    source.normalizerRoot (ownNormalizerRoot P psi V source hprimeTo normalizers)
    (fun W => surjectiveRoot_compatible source.normalizerRoot (ownNormalizerMap P psi V)
      (ownNormalizerMap_surjective P psi V hprimeTo normalizers) W.ρ)
    (ownNormalizerKernelTrivial P psi V source compatibility hrawBlock hprimeTo)

theorem ownNormalizerBrauer_reduction :
    NormalizerInflatedReduction
      (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers).subgroup
      (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers).localCharacter
      (ownNormalizerRoot P psi V source hprimeTo normalizers)
      (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers) := by
  let Z0 := centralCharacterKernel P psi
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let f := ownNormalizerMap P psi V
  let Wbar := ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers
  let qN := rawNormalizerQuotientMap V
  let qNbar := QuotientGroup.mk'
    (Wbar.subgroup.subgroupOf (Subgroup.normalizer (Wbar.subgroup : Set (CentralCharacterQuotient P psi))))
  have hcard : Nat.card f.ker = Nat.card Z0 := by
    rw [show f = normalizerMap (QuotientGroup.mk' Z0) V.subgroup from rfl,
      centralNormalizerMap_ker]
    exact Nat.card_congr (localCentralKernelEquiv Z0 V.subgroup inf_le_left).toEquiv
  have hcoprime : (Nat.card f.ker).Coprime P.p := by
    rw [hcard]
    exact (P.iota.prime.coprime_iff_not_dvd.mpr hprimeTo).symm
  intro nbar
  obtain ⟨n, rfl⟩ :=
    primeRegularElement_map_surjective_of_ker_card_coprime f
      (ownNormalizerMap_surjective P psi V hprimeTo normalizers) hcoprime nbar
  have hsquare : qNbar (f n.1) = qW Z0 V.subgroup (qN n.1) :=
    DFunLike.congr_fun (qW_quotient_square Z0 V.subgroup) n.1
  have hord := congrFun
    (ownQuotientWeight_character_factorization P psi V source
      compatibility hrawBlock hprimeTo normalizers) (qN n.1)
  have hbr := congrArg (fun chi : PrimeRegularClassFunction P.K N P.p => chi n)
    (ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock hprimeTo normalizers)
  calc
    Wbar.localCharacter (qNbar (f n.1)) =
        Wbar.localCharacter (qW Z0 V.subgroup (qN n.1)) :=
      congrArg Wbar.localCharacter hsquare
    _ = V.localCharacter (qN n.1) := hord.symm
    _ = source.localBrauer.1 n := source.localBrauer_reduction n
    _ = (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1
        (PrimeRegularElement.map f n) := hbr.symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
