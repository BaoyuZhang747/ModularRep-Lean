import Formalisation.C2Cancellation
import ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings

/-!
# The Fischer prime three signature cancellation

This file checks the numerical cancellation used for `Fi'_24` at the
coefficient prime three.  It does not identify transcript rows with literal
characters, blocks, or weights.

The source interface records only the semantic identification of the three
Brauer rows, the two already known weight signatures, and equality of the
orbit data for the complete sector.  Lean derives equality for the two known
block parts from their signatures and then derives the principal part by
cancellation.
-/

namespace ModularRep.PaperProofs.SporadicFi24ThreeSignatureCancellation

open Formalisation.C2Cancellation
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings

/-- Retain the total and fixed point coordinates from each printed
`(l,fixed,free2)` row. -/
def fi24ThreeSignaturesFromTranscript : List (Nat × Nat) :=
  fi24ThreePrintedRowsFromTranscript.map
    (fun row => (row.1, row.2.1))

theorem fi24ThreeSignaturesFromTranscript_exact :
    fi24ThreeSignaturesFromTranscript =
      [(25, 25), (4, 2), (1, 1)] := by
  simp [fi24ThreeSignaturesFromTranscript, fi24ThreePrintedRows_exact]

/-- The two block parts already known before principal block cancellation. -/
inductive Fi24ThreeKnownBlock
  | nonprincipal
  | defectZero
  deriving DecidableEq

instance : Fintype Fi24ThreeKnownBlock :=
  ⟨{.nonprincipal, .defectZero}, by
    intro block
    cases block <;> simp⟩

/-- Minimal semantic boundary for the prime three cancellation.

`principalBrauer` and `principalWeight` are the orbit data of the two
principal block fibres.  The functions `knownBrauer` and `knownWeight` give
the nonprincipal and defect zero parts.  The three row identifications remain
external.  No actual set of characters or weights is represented here.
-/
structure Fi24ThreeSignatureSource where
  principalBrauer : C2OrbitData
  principalWeight : C2OrbitData
  knownBrauer : Fi24ThreeKnownBlock → C2OrbitData
  knownWeight : Fi24ThreeKnownBlock → C2OrbitData
  completeSectorOrbitData :
    decompositionData principalBrauer knownBrauer =
      decompositionData principalWeight knownWeight
  brauerRows :
    [signature principalBrauer,
     signature (knownBrauer .nonprincipal),
     signature (knownBrauer .defectZero)] =
      fi24ThreeSignaturesFromTranscript
  nonprincipalWeightSignature :
    signature (knownWeight .nonprincipal) = (4, 2)
  defectZeroWeightSignature :
    signature (knownWeight .defectZero) = (1, 1)

namespace Fi24ThreeSignatureSource

theorem brauerRows_exact (source : Fi24ThreeSignatureSource) :
    [signature source.principalBrauer,
     signature (source.knownBrauer .nonprincipal),
     signature (source.knownBrauer .defectZero)] =
      [(25, 25), (4, 2), (1, 1)] :=
  source.brauerRows.trans fi24ThreeSignaturesFromTranscript_exact

/-- Equality of signatures determines the orbit data of each already known
block part. -/
theorem knownOrbitData_eq (source : Fi24ThreeSignatureSource) :
    ∀ block, source.knownBrauer block = source.knownWeight block := by
  have hBrauer := source.brauerRows_exact
  simp only [List.cons.injEq, and_true] at hBrauer
  intro block
  cases block with
  | nonprincipal =>
      exact signature_injective
        (hBrauer.2.1.trans source.nonprincipalWeightSignature.symm)
  | defectZero =>
      exact signature_injective
        (hBrauer.2.2.trans source.defectZeroWeightSignature.symm)

/-- Cancellation of the two known parts determines the principal orbit
data. -/
theorem principalOrbitData_eq (source : Fi24ThreeSignatureSource) :
    source.principalBrauer = source.principalWeight :=
  cancel_decomposition source.completeSectorOrbitData
    source.knownOrbitData_eq

theorem principalBrauerSignature (source : Fi24ThreeSignatureSource) :
    signature source.principalBrauer = (25, 25) := by
  have hRows := source.brauerRows_exact
  simp only [List.cons.injEq, and_true] at hRows
  exact hRows.1

/-- The principal weight signature is a conclusion of cancellation, not a
source field. -/
theorem principalWeightSignature (source : Fi24ThreeSignatureSource) :
    signature source.principalWeight = (25, 25) := by
  calc
    signature source.principalWeight =
        signature source.principalBrauer :=
      congrArg signature source.principalOrbitData_eq.symm
    _ = (25, 25) := source.principalBrauerSignature

theorem principalSignatures
    (source : Fi24ThreeSignatureSource) :
    signature source.principalBrauer = (25, 25) ∧
      signature source.principalWeight = (25, 25) :=
  ⟨source.principalBrauerSignature, source.principalWeightSignature⟩

end Fi24ThreeSignatureSource

end ModularRep.PaperProofs.SporadicFi24ThreeSignatureCancellation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
