import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDuplicateColumnSymmetrization

open SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
open SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank

universe u v w
variable {K : Type u} [Field K] [CharZero K]
variable {Row : Type v} {Column : Type w}

def precompLinear {I J : Type*} (q : I → J) : (J → K) →ₗ[K] (I → K) where
  toFun f := f ∘ q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinate_plus_finrank
    (sigma : Equiv.Perm (Fin 41))
    (hsigma : Function.Involutive sigma)
    (hfixed : Nat.card (Function.fixedPoints sigma) = 31) :
    Module.finrank K (LinearMap.range
      (LinearMap.id + precompLinear (K := K) sigma)) = 36 := by
  classical
  have hB : ∀ i : Fin 41,
      precompLinear (K := K) sigma (Pi.basisFun K (Fin 41) i) =
        Pi.basisFun K (Fin 41) (sigma i) := by
    intro i
    have hsymm : sigma.symm i = sigma i := by
      apply sigma.injective
      rw [sigma.apply_symm_apply, hsigma i]
    change (Pi.basisFun K (Fin 41) i) ∘ sigma = _
    rw [Pi.basisFun_apply, Pi.basisFun_apply, Pi.single_comp_equiv, hsymm]
  have h := fixed_card_add_card_eq_two_mul_plus_rank
    (Pi.basisFun K (Fin 41)) (precompLinear (K := K) sigma) sigma hB hsigma
  have hcard : Nat.card (Fin 41) = 41 := by simp
  rw [hfixed, hcard] at h
  omega

theorem symmetrizedRows_finrank_of_duplicate_columns
    (matrix : Row → Column → K)
    (rawCertificate : FiniteRowRankCertificate K matrix 41)
    (q : Column → Fin 41) (s : Fin 41 → Column)
    (hqs : ∀ j, q (s j) = j)
    (hduplicate : ∀ r c, matrix r c = matrix r (s (q c)))
    (perm : Column → Column) (sigma : Equiv.Perm (Fin 41))
    (hsquare : ∀ c, q (perm c) = sigma (q c))
    (hsigma : Function.Involutive sigma)
    (hfixed : Nat.card (Function.fixedPoints sigma) = 31) :
    Module.finrank K (Submodule.span K
      (Set.range fun r c => matrix r c + matrix r (perm c))) = 36 := by
  classical
  let M : Row → Fin 41 → K := fun r j => matrix r (s j)
  let E : (Fin 41 → K) →ₗ[K] (Column → K) := precompLinear q
  let P : (Fin 41 → K) →ₗ[K] (Fin 41 → K) := precompLinear sigma
  have hE : Function.Injective E := by
    intro f g h
    funext j
    have h' := congrFun h (s j)
    change f (q (s j)) = g (q (s j)) at h'
    simpa only [hqs j] using h'
  have hmap : (Submodule.span K (Set.range M)).map E =
      Submodule.span K (Set.range matrix) := by
    rw [Submodule.map_span]
    apply congrArg (Submodule.span K)
    ext y
    constructor
    · rintro ⟨v, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, funext fun c => hduplicate r c⟩
    · rintro ⟨r, rfl⟩
      exact ⟨M r, ⟨r, rfl⟩, funext fun c => (hduplicate r c).symm⟩
  have hspan : Submodule.span K (Set.range M) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      Module.finrank K (Submodule.span K (Set.range M)) =
          Module.finrank K ((Submodule.span K (Set.range M)).map E) :=
        (Submodule.equivMapOfInjective E hE _).finrank_eq
      _ = Module.finrank K (Submodule.span K (Set.range matrix)) := by rw [hmap]
      _ = 41 := rawCertificate.rows_finrank
      _ = Module.finrank K (Fin 41 → K) := by
        simp [Module.finrank_fintype_fun_eq_card]
  have hEval : ∀ r c, E (M r) c = matrix r c := by
    intro r c
    exact (hduplicate r c).symm
  have hAction : ∀ r c, E (P (M r)) c = matrix r (perm c) := by
    intro r c
    change matrix r (s (sigma (q c))) = matrix r (perm c)
    rw [← hsquare c]
    exact (hduplicate r (perm c)).symm
  have hsym : (LinearMap.range (LinearMap.id + P)).map E =
      Submodule.span K (Set.range fun r c => matrix r c + matrix r (perm c)) :=
    map_range_id_add_eq_span_symmetrizedRows M hspan E P matrix perm hEval hAction
  calc
    Module.finrank K (Submodule.span K
        (Set.range fun r c => matrix r c + matrix r (perm c))) =
        Module.finrank K ((LinearMap.range (LinearMap.id + P)).map E) :=
      congrArg (fun S : Submodule K (Column → K) => Module.finrank K S) hsym.symm
    _ = Module.finrank K (LinearMap.range (LinearMap.id + P)) :=
      (Submodule.equivMapOfInjective E hE _).finrank_eq.symm
    _ = 36 := coordinate_plus_finrank (K := K) sigma hsigma hfixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDuplicateColumnSymmetrization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
