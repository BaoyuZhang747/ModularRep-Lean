import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalClassLocalCounts

/-! The complete corrected Table 8 determines fixedness and local four-row counts
for any representative of a radical class, independently of its printed index. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTable8RadicalConsequences

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia
open SporadicProposition57ComputationRelative
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierRadicalClassLocalCounts

theorem table8_total_four_fixed_two :
    ∀ e ∈ correctedFi24Table8AtTwo, e.total = 4 → e.fixed = 2 := by
  decide

universe u v
variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Fintype G]
variable {Row : Fin 34 → Type v}
variable (C : Catalogue p K G (Fin 34) Row) (tau : MulAut G)

theorem radical_class_fixed_of_catalogue
    (hclasses : ∀ i, MulOpposite.op tau •
      (Quotient.mk'' (C.representative i) : RadicalConjugacyClass (p := p) (G := G)) =
        Quotient.mk'' (C.representative i))
    (Q : RadicalSubgroup (p := p) (G := G)) :
    MulOpposite.op tau • (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)) =
      Quotient.mk'' Q := by
  obtain ⟨i, hi⟩ := C.radical_bijective.2 (Quotient.mk'' Q)
  simpa only [hi] using hclasses i

theorem corrected_four_rows_fixed_two_of_table
    (hclasses : ∀ i, MulOpposite.op tau •
      (Quotient.mk'' (C.representative i) : RadicalConjugacyClass (p := p) (G := G)) =
        Quotient.mk'' (C.representative i))
    (entry : Fin 34 → TableSignatureEntry)
    (htable : (List.ofFn entry).Perm correctedFi24Table8AtTwo)
    (htotal : ∀ i, Nat.card (LocalDefectZeroCharacter (K := K) (C.representative i)) =
      (entry i).total)
    (hfixed : ∀ j : C.FixedIndex tau, Nat.card (ActualFixedLocal C tau j) =
      (entry j.1).fixed)
    (Q : RadicalSubgroup (p := p) (G := G)) (g : G)
    (stable : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1)
    (rows : Fin 4 → LocalDefectZeroCharacter (K := K) Q)
    (hrows : Function.Bijective rows) :
    Nat.card {r : Fin 4 // OrdinaryIrreducibleCharacter.twist K _ (rows r).1
      (localAut Q.1 (tau * MulAut.conj g) stable) = (rows r).1} = 2 := by
  obtain ⟨i, hi⟩ := C.radical_bijective.2 (Quotient.mk'' Q)
  have hQcard : Nat.card (LocalDefectZeroCharacter (K := K) Q) = 4 :=
    (Nat.card_congr (Equiv.ofBijective rows hrows).symm).trans (by simp)
  have hitotal : (entry i).total = 4 :=
    (htotal i).symm.trans
      ((local_card_eq_of_radicalClass_eq C.prime (C.representative i) Q hi).trans hQcard)
  have himem : entry i ∈ correctedFi24Table8AtTwo :=
    htable.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hifixed : (entry i).fixed = 2 := table8_total_four_fixed_two (entry i) himem hitotal
  let j : C.FixedIndex tau := ⟨i, hclasses i⟩
  calc
    Nat.card {r : Fin 4 // OrdinaryIrreducibleCharacter.twist K _ (rows r).1
        (localAut Q.1 (tau * MulAut.conj g) stable) = (rows r).1} =
        Nat.card {theta : LocalDefectZeroCharacter (K := K) Q //
          OrdinaryIrreducibleCharacter.twist K _ theta.1
            (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1} := by
      exact Nat.card_congr ((Equiv.ofBijective rows hrows).subtypeEquiv (fun _ => Iff.rfl))
    _ = Nat.card {w : WeightRadicalFibre (K := K) Q // MulOpposite.op tau • w.1 = w.1} :=
      Nat.card_congr (correctedLocalFixedEquiv C.prime Q tau g stable)
    _ = Nat.card {w : WeightRadicalFibre (K := K) (C.representative i) //
        MulOpposite.op tau • w.1 = w.1} :=
      fixed_fibre_card_eq_of_radicalClass_eq Q (C.representative i) tau hi.symm
    _ = Nat.card (C.FixedLocalRow tau j) := Nat.card_congr (C.fixedRowEquiv tau j).symm
    _ = Nat.card (ActualFixedLocal C tau j) := Nat.card_congr (fixedLocalRowEquivActual C tau j)
    _ = (entry i).fixed := hfixed j
    _ = 2 := hifixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTable8RadicalConsequences


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
