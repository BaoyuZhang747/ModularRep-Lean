import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnLocalKernel
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalOrdinaryDescent

/-! A literal weight on the quotient by its matched Brauer character's
own central kernel. The ordinary character and defect-zero property are
derived from the same raw weight and the proved kernel constancy. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnLocalKernel
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient
open ModularRep.PaperProofs.CentralEllPrimeWeightLocalOrdinaryDescent

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

def ownQuotientWeight : CharacterWeight P.p P.K (CentralCharacterQuotient P psi) where
  prime := P.iota.prime
  subgroup := V.subgroup.map (centralCharacterQuotientMap P psi)
  radical := normalizers.radical_image
  localCharacter := qWDescendedOrdinary (centralCharacterKernel P psi) inf_le_left hprimeTo
    V.subgroup V.radical normalizers V.localCharacter
    (own_weight_character_constant_on_quotient_kernel P psi V source compatibility hrawBlock hprimeTo)
  defectZero := qWDescendedOrdinary_defectZero (centralCharacterKernel P psi) inf_le_left hprimeTo
    V.subgroup V.radical normalizers V.localCharacter
    (own_weight_character_constant_on_quotient_kernel P psi V source compatibility hrawBlock hprimeTo)
    V.defectZero

theorem ownQuotientWeight_subgroup :
    (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers).subgroup =
      V.subgroup.map (centralCharacterQuotientMap P psi) := rfl

theorem ownQuotientWeight_character_factorization :
    V.localCharacter.1 = fun x : NormalizerQuotient V.subgroup =>
      (ownQuotientWeight P psi V source compatibility hrawBlock hprimeTo normalizers).localCharacter
        (qW (centralCharacterKernel P psi) V.subgroup x) :=
  qWDescendedOrdinary_factorisation (centralCharacterKernel P psi) inf_le_left hprimeTo
    V.subgroup V.radical normalizers V.localCharacter
    (own_weight_character_constant_on_quotient_kernel P psi V source compatibility hrawBlock hprimeTo)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientWeight



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
