import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData

/-! Complete printed fibres, D8 integer witnesses and singleton polynomial action. -/
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def dihedralRow : Fin 5 → Fin 108 := ![53, 70, 83, 94, 103]
def zeroRole : Fin 2 → Fin 5 := ![3, 4]
def zeroRow (j : Fin 2) : Fin 1 → Fin 108 := fun _ => (![96, 97] : Fin 2 → Fin 108) j

theorem dihedral_fibre : ∀ r, printedBlockLabel r = 2 ↔
    ∃ i : Fin 5, dihedralRow i = r := by decide
theorem zero_fibre : ∀ j r, printedBlockLabel r = zeroRole j ↔
    ∃ i : Fin 1, zeroRow j i = r := by decide

def dihedralIntegerRow (r : Fin 5) (c : Fin 91) : ℤ :=
  (rawRow (dihedralRow r) c).headD 0
theorem dihedralConstantChecks : ∀ r c,
    checkEq (rawRow (dihedralRow r) c) [dihedralIntegerRow r c] = true := by decide
theorem dihedralFixedChecks : ∀ r c,
    dihedralIntegerRow r (fullIndex c) = dihedralIntegerRow r c := by decide

def dihedralBasis : Fin 3 → Fin 5 := ![0, 1, 2]
def dihedralPivot : Fin 3 → Fin 91 := ![46, 63, 85]
def dihedralNumerator : Fin 3 → Fin 3 → ℤ := ![![0, 1, 0], ![0, 0, -1], ![-1, 0, 1]]
def dihedralCoefficients : Fin 5 → Fin 3 → ℤ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 1, 1], ![0, 1, 1]]
theorem dihedralInverseChecks : ∀ a b,
    (∑ j : Fin 3, dihedralIntegerRow (dihedralBasis a) (dihedralPivot j) *
      dihedralNumerator j b) = if a = b then 1 else 0 := by decide
theorem dihedralReconstructionChecks : ∀ r c,
    dihedralIntegerRow r c = ∑ a : Fin 3,
      dihedralCoefficients r a * dihedralIntegerRow (dihedralBasis a) c := by decide

theorem rootTag_fixed : ∀ c, columnTag (columnLabel (fullIndex c)) =
    columnTag (columnLabel c) := by decide
theorem zeroPolynomial_fixed : ∀ j c,
    rawRow (zeroRow j 0) (fullIndex c) = rawRow (zeroRow j 0) c := by decide
theorem zeroUnitCheck : ∀ j, rawRow (zeroRow j 0) (57 : Fin 91) = [1] := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
