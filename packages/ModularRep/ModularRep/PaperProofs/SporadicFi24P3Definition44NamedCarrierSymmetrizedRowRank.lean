import Mathlib.Algebra.Module.Submodule.Equiv
import ModularRep.PaperProofs.FiniteRowRankCertificate

/-! # Rank of the symmetrized generator rows -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank

universe u v w x
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Row : Type w} {Column : Type x}

theorem span_subtype_generators_eq_top (rows : Row → V) :
    Submodule.span K (Set.range fun r =>
      (⟨rows r, Submodule.subset_span (Set.mem_range_self r)⟩ :
        Submodule.span K (Set.range rows))) = ⊤ := by
  exact (Submodule.span_range_subtype_eq_top_iff
    (Submodule.span K (Set.range rows))
    (fun r => Submodule.subset_span (Set.mem_range_self r))).mpr rfl

theorem map_range_id_add_eq_span_symmetrizedRows
    (g : Row → V) (hspan : Submodule.span K (Set.range g) = ⊤)
    (E : V →ₗ[K] (Column → K)) (T : V →ₗ[K] V)
    (matrix : Row → Column → K) (perm : Column → Column)
    (hEval : ∀ r c, E (g r) c = matrix r c)
    (hAction : ∀ r c, E (T (g r)) c = matrix r (perm c)) :
    (LinearMap.range (LinearMap.id + T)).map E =
      Submodule.span K (Set.range fun r c => matrix r c + matrix r (perm c)) := by
  let F : V →ₗ[K] (Column → K) := E.comp (LinearMap.id + T)
  have hF : ∀ r, F (g r) = (fun c => matrix r c + matrix r (perm c)) := by
    intro r
    funext c
    change E (g r + T (g r)) c = _
    simpa only [map_add, Pi.add_apply] using
      congrArg₂ (fun a b : K => a + b) (hEval r c) (hAction r c)
  calc
    (LinearMap.range (LinearMap.id + T)).map E = LinearMap.range F :=
      (LinearMap.range_comp (LinearMap.id + T) E).symm
    _ = (⊤ : Submodule K V).map F := LinearMap.range_eq_map F
    _ = (Submodule.span K (Set.range g)).map F := by rw [hspan]
    _ = Submodule.span K (F '' Set.range g) := Submodule.map_span F _
    _ = Submodule.span K
        (Set.range fun r c => matrix r c + matrix r (perm c)) := by
      apply congrArg (Submodule.span K)
      ext y
      constructor
      · rintro ⟨v, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, (hF r).symm⟩
      · rintro ⟨r, rfl⟩
        exact ⟨g r, ⟨r, rfl⟩, hF r⟩

theorem finrank_range_id_add_eq_of_certificate
    (g : Row → V) (hspan : Submodule.span K (Set.range g) = ⊤)
    (E : V →ₗ[K] (Column → K)) (hE : Function.Injective E)
    (T : V →ₗ[K] V)
    (matrix : Row → Column → K) (perm : Column → Column)
    (hEval : ∀ r c, E (g r) c = matrix r c)
    (hAction : ∀ r c, E (T (g r)) c = matrix r (perm c))
    {r : ℕ} (plusCertificate : FiniteRowRankCertificate K
      (fun i c => matrix i c + matrix i (perm c)) r) :
    Module.finrank K (LinearMap.range (LinearMap.id + T)) = r := by
  calc
    Module.finrank K (LinearMap.range (LinearMap.id + T)) =
        Module.finrank K ((LinearMap.range (LinearMap.id + T)).map E) :=
      (Submodule.equivMapOfInjective E hE _).finrank_eq
    _ = Module.finrank K
        (Submodule.span K (Set.range fun i c => matrix i c + matrix i (perm c))) := by
      rw [map_range_id_add_eq_span_symmetrizedRows g hspan E T matrix perm hEval hAction]
    _ = r := plusCertificate.rows_finrank

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
