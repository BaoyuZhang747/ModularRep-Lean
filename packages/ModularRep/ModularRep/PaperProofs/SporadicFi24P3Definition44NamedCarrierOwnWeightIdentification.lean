import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

/-! Literal uniqueness of the own quotient weight from its subgroup and
ordinary factorization. The quotient radical is trivial exactly when the
original radical is trivial; this preserves the original Q=1 branch. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnWeightIdentification

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

universe u

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H)

theorem mapped_radical_eq_bot_iff
    (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi)) :
    V.subgroup.map (centralCharacterQuotientMap P psi) = ⊥ ↔ V.subgroup = ⊥ := by
  constructor
  · intro h
    have hle : V.subgroup ≤ centralCharacterKernel P psi := by
      have hk := (Subgroup.map_eq_bot_iff V.subgroup).mp h
      simpa only [centralCharacterQuotientMap, QuotientGroup.ker_mk'] using hk
    apply bot_unique
    intro x hx
    have htrivial := hom_eq_one_of_pGroup_of_primeTo_card P.iota.prime
      V.radical.isPGroup hprimeTo (Subgroup.inclusion hle) ⟨x, hx⟩
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val htrivial)
  · intro h
    rw [h, Subgroup.map_bot]

variable (source : CanonicalRawReduction P.iota V)
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

theorem ownQuotientWeight_unique
    (U : CharacterWeight P.p P.K (CentralCharacterQuotient P psi))
    (hQ : U.subgroup = V.subgroup.map (centralCharacterQuotientMap P psi))
    (hfactor : V.localCharacter.1 = fun x : NormalizerQuotient V.subgroup =>
      castLocalCharacter hQ U.localCharacter (qW (centralCharacterKernel P psi) V.subgroup x)) :
    U = ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers := by
  apply CharacterWeight.eq_of_isomorphic
  refine ⟨hQ, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro y
  obtain ⟨x, rfl⟩ := qW_surjective_ofNavarroTiep (centralCharacterKernel P psi)
    inf_le_left hprimeTo V.subgroup V.radical normalizers y
  exact (congrFun hfactor x).symm.trans
    (congrFun (ownQuotientWeight_character_factorization P psi V source compatibility
      hrawBlock hprimeTo normalizers) x)

theorem ownQuotientWeight_subgroup_eq_bot_iff :
    (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers).subgroup = ⊥ ↔
      V.subgroup = ⊥ :=
  mapped_radical_eq_bot_iff P psi V hprimeTo

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnWeightIdentification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
