import Mathlib.Data.Fintype.Fin
import Mathlib.SetTheory.Cardinal.Finite

/-! # Finite ordinary-row multiplicities without a selected row -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteRowHistograms

theorem natCard_fibre_eq_count_of_ofFn_perm
    {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (histogram : List α)
    (h : (List.ofFn f).Perm histogram) (a : α) :
    Nat.card {i : Fin n // f i = a} = histogram.count a := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ = (List.ofFn f).count a := by
      simpa only [List.Vector.get_ofFn, List.Vector.toList_ofFn] using
        (Fin.card_filter_univ_eq_vector_get_eq_count a (List.Vector.ofFn f))
    _ = histogram.count a := h.count_eq a

theorem natCard_hit_fin4_of_histogram (hit : Fin 4 → Bool)
    (h : (List.ofFn hit).Perm [false, false, false, true]) :
    Nat.card {r : Fin 4 // hit r = true} = 1 := by
  simpa using natCard_fibre_eq_count_of_ofFn_perm hit [false, false, false, true] h true

theorem natCard_hit_fin1_of_histogram (hit : Fin 1 → Bool)
    (h : (List.ofFn hit).Perm [true]) :
    Nat.card {r : Fin 1 // hit r = true} = 1 := by
  simpa using natCard_fibre_eq_count_of_ofFn_perm hit [true] h true

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteRowHistograms


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
