import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialSums

/-! Complete faithful block labels and closed five-row polynomial witnesses. -/
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def faithfulPrintedBlockLabel : Fin 74 → Fin 2 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
def faithfulSmallRow : Fin 5 → Fin 74 := ![47, 48, 53, 54, 65]
theorem faithfulSmall_fibre : ∀ r, faithfulPrintedBlockLabel r = 1 ↔
    ∃ i : Fin 5, faithfulSmallRow i = r := by decide

def smallBasis : Fin 2 → Fin 5 := ![0, 2]
def smallPivot : Fin 2 → Fin 91 := ![31, 85]
def smallMinor : Fin 2 → Fin 2 → ℤ := ![![3, 0], ![-1, 1]]
def smallNumerator : Fin 2 → Fin 2 → ℤ := ![![1, 0], ![1, 3]]
def smallCoefficients : Fin 5 → Fin 2 → ℤ := ![![1, 0], ![1, 0], ![0, 1], ![0, 1], ![1, 1]]

theorem smallPivotChecks : ∀ a j,
    checkEq (rawRow (faithfulSmallRow (smallBasis a)) (smallPivot j))
      [smallMinor a j] = true := by decide
theorem smallInverseChecks : ∀ a b,
    (∑ j : Fin 2, smallMinor a j * smallNumerator j b) =
      if a = b then 3 else 0 := by decide
theorem smallReconstructionChecks : ∀ r c,
    checkEq (rawRow (faithfulSmallRow r) c)
      (sumFin fun a : Fin 2 => scale (smallCoefficients r a)
        (rawRow (faithfulSmallRow (smallBasis a)) c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
