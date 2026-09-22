import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality

open SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank

universe u v w x
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Row : Type w} {Column : Type x}

theorem finrank_range_id_add_eq_symmetrizedRows
    (g : Row → V) (hspan : Submodule.span K (Set.range g) = ⊤)
    (E : V →ₗ[K] (Column → K)) (hE : Function.Injective E)
    (T : V →ₗ[K] V)
    (matrix : Row → Column → K) (perm : Column → Column)
    (hEval : ∀ r c, E (g r) c = matrix r c)
    (hAction : ∀ r c, E (T (g r)) c = matrix r (perm c)) :
    Module.finrank K (LinearMap.range (LinearMap.id + T)) =
      Module.finrank K (Submodule.span K
        (Set.range fun r c => matrix r c + matrix r (perm c))) := by
  calc
    Module.finrank K (LinearMap.range (LinearMap.id + T)) =
        Module.finrank K ((LinearMap.range (LinearMap.id + T)).map E) :=
      (Submodule.equivMapOfInjective E hE _).finrank_eq
    _ = _ := by
      rw [map_range_id_add_eq_span_symmetrizedRows g hspan E T matrix perm hEval hAction]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
