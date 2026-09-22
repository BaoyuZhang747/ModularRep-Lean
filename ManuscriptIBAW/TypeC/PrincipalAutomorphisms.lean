import ManuscriptIBAW.TypeC.PrincipalEquivariance

/-!
# Principal automorphism structure from the concrete group geometry

The natural projective automorphism map and the canonical full cover lift
give the required generators of the symplectic automorphism group. The
square of the selected diagonal is inner because its image in the actual
conformal quotient has order dividing two. Neither conclusion is a further
source assumption.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness

universe u

variable {n : ℕ} {F : Type u} [Field F] [Fintype F]
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (O : LiteralDiagonalFieldRealisation n F) (M : ProjectiveMultiplierSource C)
variable (cover : OddSymplecticFullCoverSource n F)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))

include S M cover L in
/-- Every actual symplectic automorphism has an inner, diagonal and field
factorization through the fixed projective map and its unique cover lift. -/
theorem principal_automorphism_two_forms (a : MulAut (Sp n F)) :
    ∃ (g : Sp n F) (sigma : F ≃+* F),
      a = MulAut.conj g * spFieldAut (n := n) sigma ∨
        a = MulAut.conj g * O.outer.diagonal.unop * spFieldAut (n := n) sigma := by
  let t := S.fullAut.symm (projectiveAutHom a)
  have ha : a = pcspToSpAut S cover L t.left * spFieldAut (n := n) t.right := by
    apply (L.bijective_on_full_cover cover).1
    rw [map_mul, projective_pcspToSpAut, ← field_projectiveAutHom]
    change projectiveAutHom a =
      S.fullAut (SemidirectProduct.inl t.left) * pspFieldAction t.right
    rw [← S.fullAut_field, ← map_mul, SemidirectProduct.inl_left_mul_inr_right]
    exact (S.fullAut.apply_symm_apply (projectiveAutHom a)).symm
  obtain ⟨g, hg | hg⟩ := pcspToSpAut_two_forms S O M cover L t.left
  · exact ⟨g, t.right, Or.inl (ha.trans (congrArg (fun b => b * spFieldAut t.right) hg))⟩
  · exact ⟨g, t.right, Or.inr (ha.trans (congrArg (fun b => b * spFieldAut t.right) hg))⟩

include S M cover L in
/-- Inner, entrywise field and the selected diagonal automorphism generate
the whole symplectic automorphism group. -/
theorem principal_automorphism_generated : Subgroup.closure
    (principalTrivialGenerators (n := n) (F := F) ∪ {principalDiagonal O}) = ⊤ := by
  let H := Subgroup.closure
    (principalTrivialGenerators (n := n) (F := F) ∪ {principalDiagonal O})
  have hinner (g : Sp n F) : MulAut.conj g ∈ H :=
    Subgroup.subset_closure (Or.inl (Or.inl ⟨g, rfl⟩))
  have hfield (sigma : F ≃+* F) : spFieldAut (n := n) sigma ∈ H :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨sigma, rfl⟩))
  have hdiagonal : O.outer.diagonal.unop ∈ H := by
    have h : principalDiagonal O ∈ H := Subgroup.subset_closure (Or.inr rfl)
    simpa only [principalDiagonal, inv_inv] using H.inv_mem h
  apply top_unique
  intro a _
  obtain ⟨g, sigma, ha | ha⟩ := principal_automorphism_two_forms S O M cover L a
  · rw [ha]
    exact H.mul_mem (hinner g) (hfield sigma)
  · rw [ha]
    exact H.mul_mem (H.mul_mem (hinner g) hdiagonal) (hfield sigma)

include S cover L in
/-- The inverse selected diagonal squares to an inner automorphism. The
proof uses its actual image in the conformal quotient of cardinality two. -/
theorem principal_diagonal_square_inner : ∃ g : Sp n F,
    principalDiagonal O * principalDiagonal O = MulAut.conj g := by
  let _ := S.normal_image
  let H := (pspEmbedding C).range
  let q : PCSp n F →* PCSp n F ⧸ H := QuotientGroup.mk' H
  have hsquare : (diagonalPCSp O)⁻¹ * (diagonalPCSp O)⁻¹ ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((diagonalPCSp O)⁻¹ * (diagonalPCSp O)⁻¹) = 1
    rw [map_mul, map_inv]
    have h := pow_card_eq_one' (x := (q (diagonalPCSp O))⁻¹)
    rw [S.quotient_card, pow_two] at h
    exact h
  obtain ⟨x, hx⟩ := hsquare
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) x
  refine ⟨g, ?_⟩
  have h := congrArg (pcspToSpAut S cover L) hx
  change pcspToSpAut S cover L (pspEmbedding C (spProjection n F g)) =
    pcspToSpAut S cover L ((diagonalPCSp O)⁻¹ * (diagonalPCSp O)⁻¹) at h
  rw [pcspToSpAut_base, map_mul, map_inv, pcspToSpAut_diagonal] at h
  exact h.symm

include S M cover L in
/-- The specified group geometry gives the automorphism decomposition required
by the principal correspondence. -/
theorem principalAutomorphismSourceFromGeometry : PrincipalAutomorphismSource O where
  rank_ge_two := cover.rank_ge_two
  odd_field := cover.field_odd
  generated := principal_automorphism_generated S O M cover L
  diagonal_square_inner := principal_diagonal_square_inner S O cover L

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
