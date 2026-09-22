import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC

/-!
# The natural quotient identification for the named matched pair

The map is induced by inclusion of the literal pair normaliser into
`G_theta`. Surjectivity is derived from the proved product decomposition;
its kernel is the literal intersection with the embedded `X`.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients

open Formalisation ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC

universe u

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))

instance baseNormal : (XInGTheta P M S).Normal :=
  selectedClause3Base_normal P M.theta S

abbrev LocalBase := (XInGTheta P M S).subgroupOf (PairNormalizer P M S)

def localToGlobalQuotient : PairNormalizer P M S →*
    (GTheta P M S ⧸ XInGTheta P M S) :=
  (QuotientGroup.mk' (XInGTheta P M S)).comp (PairNormalizer P M S).subtype

theorem localToGlobalQuotient_surjective :
    Function.Surjective (localToGlobalQuotient P M S) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (XInGTheta P M S) q
  obtain ⟨x, n, hx⟩ := product_decomposition P M S g
  refine ⟨n, ?_⟩
  change QuotientGroup.mk' (XInGTheta P M S) n.1 =
    QuotientGroup.mk' (XInGTheta P M S) g
  rw [hx, map_mul]
  have hxone : QuotientGroup.mk' (XInGTheta P M S) x.1 = 1 :=
    (QuotientGroup.eq_one_iff _).mpr x.2
  rw [hxone, one_mul]

theorem localToGlobalQuotient_ker :
    LocalBase P M S = (localToGlobalQuotient P M S).ker := by
  ext n
  change n.1 ∈ XInGTheta P M S ↔ QuotientGroup.mk' (XInGTheta P M S) n.1 = 1
  exact (QuotientGroup.eq_one_iff _).symm

/-- The source's natural local-to-global quotient isomorphism. -/
def naturalQuotientEquiv :
    (PairNormalizer P M S ⧸ LocalBase P M S) ≃*
      (GTheta P M S ⧸ XInGTheta P M S) :=
  (QuotientGroup.quotientMulEquivOfEq (localToGlobalQuotient_ker P M S)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (localToGlobalQuotient P M S) (localToGlobalQuotient_surjective P M S))

theorem naturalQuotientEquiv_mk (n : PairNormalizer P M S) :
    naturalQuotientEquiv P M S (QuotientGroup.mk' (LocalBase P M S) n) =
      QuotientGroup.mk' (XInGTheta P M S) n.1 := rfl

theorem localBase_comap_pairNormalizerEquiv :
    (LocalBase P M S).comap (pairNormalizerEquiv P M S).toMonoidHom =
      SelectedPairBase P S M.weight := by
  ext n
  change (pairNormalizerEquiv P M S n).1 ∈ SelectedBrauerBase P.iota S M.theta.1 ↔
    n ∈ SelectedPairBase P S M.weight
  rw [mem_selectedBrauerBase_iff_right_eq_one, mem_selectedPairBase_iff_right_eq_one]
  rfl

theorem pairBase_map_pairNormalizerEquiv :
    (SelectedPairBase P S M.weight).map (pairNormalizerEquiv P M S).toMonoidHom =
      LocalBase P M S := by
  rw [← localBase_comap_pairNormalizerEquiv P M S]
  exact Subgroup.map_comap_eq_self_of_surjective (pairNormalizerEquiv P M S).surjective _

def pairBaseEquiv : SelectedPairBase P S M.weight ≃* LocalBase P M S :=
  ((pairNormalizerEquiv P M S).subgroupMap (SelectedPairBase P S M.weight)).trans
    (MulEquiv.subgroupCongr (pairBase_map_pairNormalizerEquiv P M S))

theorem pairBaseEquiv_square (n : SelectedPairBase P S M.weight) :
    (pairBaseEquiv P M S n).1 = pairNormalizerEquiv P M S n.1 := rfl

def rawToNamedQuotientEquiv :
    (SelectedPairStabilizer P S M.weight ⧸ SelectedPairBase P S M.weight) ≃*
      (PairNormalizer P M S ⧸ LocalBase P M S) :=
  QuotientGroup.congr _ _ (pairNormalizerEquiv P M S)
    (pairBase_map_pairNormalizerEquiv P M S)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
