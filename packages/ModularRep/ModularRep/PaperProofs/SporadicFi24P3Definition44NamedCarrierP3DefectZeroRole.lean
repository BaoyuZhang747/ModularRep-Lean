import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrincipalBrauerSupport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefectZeroRolePrelude
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierV3BlockStability
import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

/-! Derive the specified role of every global defect-zero reduction. The
four-character block and the principal block exclude both other roles.
The retained ordinary defect-zero singleton law is used without strengthening. -/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectZeroRole

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource defectZeroBrauerFibre_subsingleton)
open SporadicFi24P3Definition44Clause3ACWindow (trivialIBr)
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
open SporadicFi24P3Definition44NamedCarrierLiteralV3BlockAction
open SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature
open SporadicFi24P3Definition44NamedCarrierV3BlockStability
open SporadicFi24P3Definition44NamedCarrierPrincipalBrauerSupport
open SporadicFi24P3Definition44NamedCarrierDefectZeroRolePrelude
open SporadicFi24P3V3RawRankCertificate

universe u
variable {k K G : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem defectZero_operationsBlock_eq_role_two_of_literal_values
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
    (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ActualOrdinaryDecomposition iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks)
    (selected : Fin 6 → OrdinaryIrreducibleCharacter.Irr K G)
    (hcomplete : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ∀ chi, Dordinary.ordinaryBlock chi = roles 1 ↔ ∃ r, selected r = chi)
    (representatives : PrimeRegularRepresentativeCover 3 G (Fin 30))
    (encoding : PrimitiveTwentyNineEncoding K)
    (hvalues : ∀ r c, (selected r).1 (representatives.representative c).1 =
      literalV3Rows encoding r c)
    (D : DefectZeroReductionSource iota)
    (B : let _ := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks D)
    (hDefect : let _ := R.1.operations.ambientBlockData.fintypeBlock
      IsMaximalCentralBrauerDefect (p := 3) R.1.operations.ambientBlockData.blocks
        (roles 2) (⊥ : Subgroup G))
    (d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := G)) :
    operationsBlock iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R (D.reduce (iota := iota) d) = roles 2 := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let blocks := R.1.operations.ambientBlockData.blocks
  have hcard : Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = roles 1} = 4 :=
    actual_b1_card_four iota hinj blocks Dordinary (roles 1) selected
      hcomplete representatives encoding (literalV3Binding encoding) hvalues
  have hraw4 : Nat.card (IBrBlock iota hinj blocks (roles 1)) = 4 := by
    change Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = roles 1} = 4
    simpa only [operationsBlock_eq iota hinj R blocks] using hcard
  have hpG : 3 ∣ Nat.card G :=
    prime_dvd_card_of_ibrBlock_card_ne_one iota hinj blocks (roles 1)
      (by rw [hraw4]; decide)
  have hc1 : brauerBlock iota hinj blocks (trivialIBr iota) ≠ roles 1 :=
    trivialBrauerBlock_ne_of_ordinary_rows_vanish iota hinj blocks Dordinary
      (roles 1) selected hcomplete (representatives.representative 23)
      (fun r => (hvalues r 23).trans (literalV3Rows_zero_column encoding r))
  have hc2 : brauerBlock iota hinj blocks (trivialIBr iota) ≠ roles 2 := by
    intro h
    apply trivialBlock_ne_of_defect_bot iota hinj blocks (roles 2) hpG hDefect
    change operationsBlock iota hinj R (trivialIBr iota) = roles 2
    exact (operationsBlock_eq iota hinj R blocks (trivialIBr iota)).trans h
  have hroles (b : ActualBlock (k := k) (X := G)) :
      b = roles 0 ∨ b = roles 1 ∨ b = roles 2 := by
    obtain ⟨i, rfl⟩ := roles.surjective b
    fin_cases i <;> simp
  have hc0 : brauerBlock iota hinj blocks (trivialIBr iota) = roles 0 :=
    (hroles _).resolve_right (fun h => h.elim hc1 hc2)
  have hd1 : brauerBlock iota hinj blocks (D.reduce (iota := iota) d) ≠ roles 1 := by
    intro h
    have hsub : Subsingleton {phi : IBr iota //
        brauerBlock iota hinj blocks phi = roles 1} := by
      simpa only [h] using
        (defectZeroBrauerFibre_subsingleton
          (iota := iota) (hinj := hinj) (blocks := blocks) D B d)
    have hone : Nat.card {phi : IBr iota //
        brauerBlock iota hinj blocks phi = roles 1} = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨D.reduce (iota := iota) d, h⟩⟩⟩
    omega
  have hdc : brauerBlock iota hinj blocks (D.reduce (iota := iota) d) ≠
      brauerBlock iota hinj blocks (trivialIBr iota) := by
    intro h
    apply reduction_ne_trivial_of_dvd_card iota D hpG d
    exact (DefectZeroOrdinaryBlockSource.uniqueBrauer
      (iota := iota) (hinj := hinj) (blocks := blocks)
      D B d (trivialIBr iota) h.symm).symm
  have hd2 : brauerBlock iota hinj blocks (D.reduce (iota := iota) d) = roles 2 :=
    ((hroles _).resolve_left (fun h => hdc (h.trans hc0.symm))).resolve_left hd1
  exact (operationsBlock_eq iota hinj R blocks (D.reduce (iota := iota) d)).trans hd2

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectZeroRole


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
