import ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-! The actual outer element is non-inner because it interchanges two
classes separated by an ordinary character. Only the supplied value and
fusion identifications bind the finite V3 calculation to the actual group. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNontrivialOuterOfV3
open SporadicFi24P3V3RawRankCertificate
open SporadicFi24P3PlusRankReplayContract
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
universe u

theorem v3_last_pivot_moved {K : Type u} [Field K] [CharZero K]
    (E : PrimitiveTwentyNineEncoding K) (V3 : CanonicalSupplementV3Binding E) :
    V3.restrictionRows 4 27 ≠ V3.restrictionRows 4 28 := by
  intro heq
  have hn := V3.rawPacket.selectedEntries (3 : Fin 4) (3 : Fin 4)
  change V3.restrictionRows 4 27 = -negativePowerSum E at hn
  have hs := V3.symmetrised_rows_eq (4 : Fin 6) (27 : Fin 30)
  change V3.restrictionRows 4 27 + V3.restrictionRows 4 28 = (0 + 2 + 0) / 2 at hs
  norm_num at hs
  rw [← heq, hn] at hs
  apply positive_sub_negative_ne_zero E
  have hsum := one_add_negative_add_positive_eq_zero E
  linear_combination hsum + hs

theorem selected_outer_nontrivial_of_v3
    {K G : Type u} [Field K] [CharZero K] [Group G]
    (E : PrimitiveTwentyNineEncoding K) (V3 : CanonicalSupplementV3Binding E)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) (v : Fin 30 → G)
    (hvalues : ∀ c, chi.1 (v c) = V3.restrictionRows 4 c)
    (tau : MulAut G)
    (fusion : ∃ x : G, tau (v 27) = x * v 28 * x⁻¹) :
    QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
      (MulOpposite.op tau) ≠ 1 := by
  intro hone
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff (MulOpposite.op tau)).mp hone
  have ht : tau = MulAut.conj g⁻¹ := (congrArg MulOpposite.unop hg).symm
  obtain ⟨x, hx⟩ := fusion
  apply v3_last_pivot_moved E V3
  rw [← hvalues 27, ← hvalues 28]
  calc
    chi.1 (v 27) = chi.1 ((MulAut.conj g⁻¹) (v 27)) :=
      (ordinaryCharacter_conj chi g⁻¹ (v 27)).symm
    _ = chi.1 (tau (v 27)) := congrArg (fun a : MulAut G => chi.1 (a (v 27))) ht.symm
    _ = chi.1 (x * v 28 * x⁻¹) := congrArg chi.1 hx
    _ = chi.1 (v 28) := ordinaryCharacter_conj chi x (v 28)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNontrivialOuterOfV3


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
