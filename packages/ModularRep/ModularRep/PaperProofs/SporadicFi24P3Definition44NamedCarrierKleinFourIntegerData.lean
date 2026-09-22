import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation

/-! Four actual written table rows, finite labels and closed integer checks. -/
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierTrivialColumnData

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def selectedRow : Fin 4 → Fin 108 := ![34, 63, 64, 78]
def printedBlockLabel : Fin 108 → Fin 5 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]
def rowImage : Fin 4 → Fin 4 := ![0, 2, 1, 3]

theorem selected_fibre : ∀ r, printedBlockLabel r = 1 ↔
    ∃ i : Fin 4, selectedRow i = r := by decide

def integerRow (r : Fin 4) (c : Fin 91) : ℤ :=
  (rawRow (selectedRow r) c).headD 0

theorem constantChecks : ∀ r c,
    checkEq (rawRow (selectedRow r) c) [integerRow r c] = true := by decide

theorem rowActionChecks : ∀ r c,
    integerRow r (fullIndex c) = integerRow (rowImage r) c := by decide

def plusIntegerRow (r : Fin 4) (c : Fin 91) : ℤ :=
  integerRow r c + integerRow r (fullIndex c)

def rawBasis : Fin 3 → Fin 4 := ![0, 1, 2]
def rawPivot : Fin 3 → Fin 91 := ![57, 64, 65]
def rawNumerator : Fin 3 → Fin 3 → ℤ := ![![9, 0, 0], ![0, 5, 4], ![0, 4, 5]]
def rawCoefficients : Fin 4 → Fin 3 → ℤ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1]]

theorem rawInverseChecks : ∀ a b,
    (∑ j : Fin 3, integerRow (rawBasis a) (rawPivot j) * rawNumerator j b) =
      if a = b then 9 else 0 := by decide

theorem rawReconstructionChecks : ∀ r c,
    integerRow r c = ∑ a : Fin 3, rawCoefficients r a * integerRow (rawBasis a) c := by decide

def plusBasis : Fin 2 → Fin 4 := ![0, 1]
def plusPivot : Fin 2 → Fin 91 := ![57, 64]
def plusNumerator : Fin 2 → Fin 2 → ℤ := ![![1, 0], ![0, 2]]
def plusCoefficients : Fin 4 → Fin 2 → ℤ := ![![1, 0], ![0, 1], ![0, 1], ![1, 2]]

theorem plusInverseChecks : ∀ a b,
    (∑ j : Fin 2, plusIntegerRow (plusBasis a) (plusPivot j) * plusNumerator j b) =
      if a = b then 2 else 0 := by decide

theorem plusReconstructionChecks : ∀ r c,
    plusIntegerRow r c = ∑ a : Fin 2, plusCoefficients r a * plusIntegerRow (plusBasis a) c := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
