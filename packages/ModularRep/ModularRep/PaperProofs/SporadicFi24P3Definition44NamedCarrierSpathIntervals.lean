import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients

/-!
# The two intermediate-subgroup conventions in Spath's Lemma 6.1

The source uses local subgroups H with N_X(Q) <= H <= N_A(Q), and compares
H with XH. The concrete block API uses J with X <= J <= A and its local
intersection. The proved product decomposition identifies these intervals
by actual subgroup inclusions, not by an abstract equality of cardinalities.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathIntervals

open Formalisation ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients

universe u

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))

local instance outerFinite : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : P.H → P.H))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

def overBase (H : Subgroup (PairNormalizer P M S)) : Subgroup (GTheta P M S) :=
  XInGTheta P M S ⊔ H.map (PairNormalizer P M S).subtype

def localIntersection (J : Subgroup (GTheta P M S)) : Subgroup (PairNormalizer P M S) :=
  J.subgroupOf (PairNormalizer P M S)

theorem base_le_overBase (H : Subgroup (PairNormalizer P M S)) :
    XInGTheta P M S ≤ overBase P M S H := le_sup_left

theorem localBase_le_localIntersection (J : Subgroup (GTheta P M S))
    (hJ : XInGTheta P M S ≤ J) : LocalBase P M S ≤ localIntersection P M S J :=
  fun _ hn ↦ hJ hn

theorem localIntersection_overBase (H : Subgroup (PairNormalizer P M S))
    (hH : LocalBase P M S ≤ H) : localIntersection P M S (overBase P M S H) = H := by
  apply Subgroup.ext
  intro d
  constructor
  · intro hd
    obtain ⟨b, hb, y, hy, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hd
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
    have hbD : b ∈ PairNormalizer P M S := by
      have hb_eq : b = d.1 * h.1⁻¹ := (eq_mul_inv_iff_mul_eq).mpr heq
      rw [hb_eq]
      exact (PairNormalizer P M S).mul_mem d.2 ((PairNormalizer P M S).inv_mem h.2)
    let bD : PairNormalizer P M S := ⟨b, hbD⟩
    have hbH : bD ∈ H := hH hb
    have heqD : bD * h = d := Subtype.ext heq
    exact heqD ▸ H.mul_mem hbH hh
  · intro hd
    exact (le_sup_right : H.map (PairNormalizer P M S).subtype ≤ overBase P M S H)
      (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)

theorem overBase_localIntersection (J : Subgroup (GTheta P M S))
    (hJ : XInGTheta P M S ≤ J) : overBase P M S (localIntersection P M S J) = J := by
  apply le_antisymm
  · apply sup_le hJ
    rintro g ⟨d, hd, rfl⟩
    exact hd
  · intro g hg
    obtain ⟨b, d, heq⟩ := product_decomposition P M S g
    have hd : d ∈ localIntersection P M S J := by
      have hd_eq : d.1 = b.1⁻¹ * g := by rw [heq]; group
      change d.1 ∈ J
      rw [hd_eq]
      exact J.mul_mem (J.inv_mem (hJ b.2)) hg
    exact Subgroup.mem_sup_of_normal_left.mpr
      ⟨b.1, b.2, d.1, Subgroup.mem_map.mpr ⟨d, hd, rfl⟩, heq.symm⟩

/-- The source H <-> XH correspondence, with both subgroup orders preserved. -/
def intermediateOrderIso :
    {H : Subgroup (PairNormalizer P M S) // LocalBase P M S ≤ H} ≃o
      {J : Subgroup (GTheta P M S) // XInGTheta P M S ≤ J} where
  toFun H := ⟨overBase P M S H.1, base_le_overBase P M S H.1⟩
  invFun J := ⟨localIntersection P M S J.1, localBase_le_localIntersection P M S J.1 J.2⟩
  left_inv H := Subtype.ext (localIntersection_overBase P M S H.1 H.2)
  right_inv J := Subtype.ext (overBase_localIntersection P M S J.1 J.2)
  map_rel_iff' := by
    intro H K
    change overBase P M S H.1 ≤ overBase P M S K.1 ↔ H.1 ≤ K.1
    constructor
    · intro h d hd
      have hd' : d ∈ localIntersection P M S (overBase P M S K.1) :=
        h ((le_sup_right : H.1.map (PairNormalizer P M S).subtype ≤ overBase P M S H.1)
          (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩))
      exact (localIntersection_overBase P M S K.1 K.2) ▸ hd'
    · intro h
      exact sup_le_sup_left (Subgroup.map_mono h) _

/-- The actual local intersection inside J, used by the concrete block API. -/
abbrev InsideLocal (J : Subgroup (GTheta P M S)) :=
  (PairNormalizer P M S).subgroupOf J

def localIntersectionEquiv (J : Subgroup (GTheta P M S)) :
    localIntersection P M S J ≃* InsideLocal P M S J where
  toFun d := ⟨⟨d.1.1, d.2⟩, d.1.2⟩
  invFun d := ⟨⟨d.1.1, d.2⟩, d.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def insideLocalToNormalizer (J : Subgroup (GTheta P M S)) :
    InsideLocal P M S J →* PairNormalizer P M S where
  toFun d := ⟨d.1.1, d.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem localIntersectionEquiv_square (J : Subgroup (GTheta P M S)) :
    (insideLocalToNormalizer P M S J).comp (localIntersectionEquiv P M S J).toMonoidHom =
      (localIntersection P M S J).subtype := rfl

theorem local_restriction_square {p : ℕ} {K : Type u} [Field K]
    (J : Subgroup (GTheta P M S))
    (chi : PrimeRegularClassFunction K (PairNormalizer P M S) p) :
    PrimeRegularClassFunction.pullback (localIntersectionEquiv P M S J).toMonoidHom
      (PrimeRegularClassFunction.pullback (insideLocalToNormalizer P M S J) chi) =
    PrimeRegularClassFunction.pullback (localIntersection P M S J).subtype chi := rfl

theorem radical_le_base : QInGTheta P M S ≤ XInGTheta P M S := by
  rw [embedded_Q_identification P M S, ← xEmbedding_range P M S]
  exact (Q P M).map_le_range (xEmbedding P M S)

theorem insideLocal_eq_normalizer (J : Subgroup (GTheta P M S))
    (hJ : XInGTheta P M S ≤ J) :
    InsideLocal P M S J =
      Subgroup.normalizer ((QInGTheta P M S).subgroupOf J : Set J) :=
  Subgroup.subgroupOf_normalizer_eq ((radical_le_base P M S).trans hJ)

def sourceLocalEquiv (H : Subgroup (PairNormalizer P M S))
    (hH : LocalBase P M S ≤ H) : H ≃* InsideLocal P M S (overBase P M S H) :=
  (MulEquiv.subgroupCongr (localIntersection_overBase P M S H hH).symm).trans
    (localIntersectionEquiv P M S (overBase P M S H))

theorem sourceLocalEquiv_square (H : Subgroup (PairNormalizer P M S))
    (hH : LocalBase P M S ≤ H) :
    (insideLocalToNormalizer P M S (overBase P M S H)).comp
      (sourceLocalEquiv P M S H hH).toMonoidHom = H.subtype := rfl

theorem source_local_restriction_square {p : ℕ} {K : Type u} [Field K]
    (H : Subgroup (PairNormalizer P M S)) (hH : LocalBase P M S ≤ H)
    (chi : PrimeRegularClassFunction K (PairNormalizer P M S) p) :
    PrimeRegularClassFunction.pullback (sourceLocalEquiv P M S H hH).toMonoidHom
      (PrimeRegularClassFunction.pullback
        (insideLocalToNormalizer P M S (overBase P M S H)) chi) =
      PrimeRegularClassFunction.pullback H.subtype chi := rfl

theorem global_quotient_card_le_two :
    Nat.card (GTheta P M S ⧸ XInGTheta P M S) ≤ 2 := by
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  calc
    Nat.card (GTheta P M S ⧸ XInGTheta P M S) ≤ Nat.card (SelectedOuterGroup S) :=
      Nat.card_le_card_of_injective
        (stabilizerQuotientEmbedding (phi := selectedOuterField S) M.theta.1)
        (stabilizerQuotientEmbedding_injective (phi := selectedOuterField S) M.theta.1)
    _ ≤ 2 := selectedOuterGroup_card_le_two S

/-- Only the bottom and top block equalities are needed for this ambient group. -/
theorem intermediate_eq_base_or_top (J : Subgroup (GTheta P M S))
    (hJ : XInGTheta P M S ≤ J) : J = XInGTheta P M S ∨ J = ⊤ := by
  exact subgroup_eq_base_or_top_of_quotient_card_le_two
    (XInGTheta P M S) (global_quotient_card_le_two P M S) J hJ

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathIntervals


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
