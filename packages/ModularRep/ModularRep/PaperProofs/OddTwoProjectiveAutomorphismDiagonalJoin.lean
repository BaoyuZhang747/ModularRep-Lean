import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
import ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
import ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The actual covering automorphism map and the two projective diagonal cosets

The homomorphism Aut(Sp) -> Aut(PSp) is the canonical whole-centre quotient
map already used by central-two Brauer inflation. Its bijectivity is the
exact standard E1 automorphism-lifting theorem for the displayed universal
full cover. The source premise uses OddSymplecticFullCoverSource, including
the exceptional (n,q)=(2,3) scope; no unrelated equivalence is supplied.

The existing Feng--Malle diagonal matrix is placed in the literal CSp.
Its transpose-first similitude equation and actual conjugation square are
proved from its displayed matrices. The remaining E1 multiplier fact says
precisely that the image of a conformal matrix lies in the fixed PSp image
if and only if its multiplier is square. Together with the already fixed
index-two quotient, K derives both cosets, their actual lifted Sp
automorphisms, and the two possible actions on function-valued IBr.

There is no orbit-disjunction, character-relation, covering-character or
DGN source field. The two alternatives below are consequences of group
geometry and inner invariance; they do not supply an orbit witness for
the modular block-triple relation.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin

open ModularRep
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
  (LiteralDiagonalFieldRealisation)
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
  (OddSymplecticFullCoverSource)

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

/-- The actual full automorphism homomorphism induced by the centre quotient. -/
def projectiveAutHom : MulAut (Sp n F) →* MulAut (PSp n F) :=
  centerQuotientAutHom (Sp n F)

@[simp] theorem projectiveAutHom_projection (alpha : MulAut (Sp n F)) (g : Sp n F) :
    projectiveAutHom alpha (spProjection n F g) = spProjection n F (alpha g) := rfl

/-- This is the same pointwise map consumed by central-two Brauer inflation. -/
theorem projectiveAutHom_eq_global (alpha : MulAut (Sp n F)) :
    projectiveAutHom alpha =
      ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation.projectiveAutomorphism alpha := by
  apply DFunLike.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) x
  rfl

/-- Standard E1 lifting for THIS literal full-cover projection. Universal
central extensions lift each quotient automorphism uniquely; the source
is not a freely chosen automorphism equivalence or a character statement.
The full-cover witness is required, including its exceptional-case data. -/
structure FullCoverAutomorphismLiftingSource : Prop where
  bijective_on_full_cover : ∀ (_cover : OddSymplecticFullCoverSource n F),
    Function.Bijective (projectiveAutHom (n := n) (F := F))

/-- The automorphism equivalence is computed from the fixed quotient hom. -/
def projectiveAutEquiv (cover : OddSymplecticFullCoverSource n F)
    (L : FullCoverAutomorphismLiftingSource (n := n) (F := F)) :
    MulAut (Sp n F) ≃* MulAut (PSp n F) :=
  MulEquiv.ofBijective projectiveAutHom (L.bijective_on_full_cover cover)

@[simp] theorem projectiveAutEquiv_apply (cover : OddSymplecticFullCoverSource n F)
    (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))
    (alpha : MulAut (Sp n F)) : projectiveAutEquiv cover L alpha = projectiveAutHom alpha := rfl

theorem projectiveAutHom_inner (g : Sp n F) :
    projectiveAutHom (MulAut.conj g) = MulAut.conj (spProjection n F g) := by
  apply DFunLike.ext
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) x
  change projectiveAutHom (MulAut.conj g) (spProjection n F h) =
    MulAut.conj (spProjection n F g) (spProjection n F h)
  simp only [projectiveAutHom_projection, MulAut.conj_apply, map_mul, map_inv]

section DiagonalMatrices

variable (O : LiteralDiagonalFieldRealisation n F)

/-- The exact matrix and inverse already present in the FM source problem. -/
def diagonalGL : Matrix.GeneralLinearGroup (Coordinate n) F where
  val := O.diagonalMatrix
  inv := O.diagonalInverse
  val_inv := O.mul_inverse
  inv_val := O.inverse_mul

/-- Convert the source's row-form convention into the literal CSp
transpose-first convention, with the SAME multiplier. -/
theorem diagonal_transpose_similitude :
    O.diagonalMatrix.transpose * Matrix.J (Fin n) F * O.diagonalMatrix =
      (O.multiplier : F) • Matrix.J (Fin n) F := by
  have hleft : Matrix.J (Fin n) F * O.diagonalMatrix.transpose =
      (O.multiplier : F) • (O.diagonalInverse * Matrix.J (Fin n) F) := by
    calc
      _ = (O.diagonalInverse * O.diagonalMatrix) * Matrix.J (Fin n) F *
          O.diagonalMatrix.transpose := by rw [O.inverse_mul]; simp
      _ = O.diagonalInverse *
          (O.diagonalMatrix * Matrix.J (Fin n) F * O.diagonalMatrix.transpose) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [O.similitude, Matrix.mul_smul]
  calc
    _ = ((-Matrix.J (Fin n) F) * Matrix.J (Fin n) F) *
        O.diagonalMatrix.transpose * Matrix.J (Fin n) F * O.diagonalMatrix := by
      simp only [Matrix.neg_mul, Matrix.J_squared, neg_neg, one_mul]
    _ = (-Matrix.J (Fin n) F) *
        (Matrix.J (Fin n) F * O.diagonalMatrix.transpose) *
          Matrix.J (Fin n) F * O.diagonalMatrix := by simp only [Matrix.mul_assoc]
    _ = (O.multiplier : F) •
        ((-Matrix.J (Fin n) F) * O.diagonalInverse *
          (Matrix.J (Fin n) F * Matrix.J (Fin n) F) * O.diagonalMatrix) := by
      rw [hleft]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = (O.multiplier : F) •
        (Matrix.J (Fin n) F * O.diagonalInverse * O.diagonalMatrix) := by
      simp only [Matrix.J_squared, Matrix.mul_neg, Matrix.neg_mul, mul_one, neg_neg]
    _ = _ := by rw [Matrix.mul_assoc, O.inverse_mul, mul_one]

/-- The diagonal similitude is an element of the actual conformal group. -/
def diagonalCSp : CSp n F :=
  ⟨diagonalGL O, O.multiplier, diagonal_transpose_similitude O⟩

@[simp] theorem diagonalCSp_matrix : cspMatrix n F (diagonalCSp O) = O.diagonalMatrix := rfl

/-- Its actual whole-centre quotient class. -/
def diagonalPCSp : PCSp n F := cspProjection n F (diagonalCSp O)

/-- Matrix-level agreement of the FM automorphism with conjugation in CSp. -/
theorem diagonalCSp_conjugates_sp (g : Sp n F) :
    spEmbedding n F (O.outer.diagonal.unop g) =
      diagonalCSp O * spEmbedding n F g * (diagonalCSp O)⁻¹ := by
  apply cspMatrix_injective n F
  change (O.outer.diagonal.unop g : Matrix (Coordinate n) (Coordinate n) F) =
    O.diagonalMatrix * (g : Matrix (Coordinate n) (Coordinate n) F) * O.diagonalInverse
  exact O.diagonal_apply g

theorem projective_diagonal_embedding (C : CenterIntersectionSource n F) (x : PSp n F) :
    pspEmbedding C (projectiveAutHom O.outer.diagonal.unop x) =
      diagonalPCSp O * pspEmbedding C x * (diagonalPCSp O)⁻¹ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) x
  change cspProjection n F (spEmbedding n F (O.outer.diagonal.unop g)) =
    diagonalPCSp O * cspProjection n F (spEmbedding n F g) * (diagonalPCSp O)⁻¹
  have h := congrArg (cspProjection n F) (diagonalCSp_conjugates_sp O g)
  simpa only [diagonalPCSp, map_mul, map_inv] using h

/-- Standard E1 scalar-centre/multiplier description on the fixed matrix
groups. Each tested multiplier is attached to its actual matrix equation.
This is the square-class kernel theorem, with no selected diagonal coset,
character action or desired orbit alternative as a source conclusion. -/
structure ProjectiveMultiplierSource (C : CenterIntersectionSource n F) : Prop where
  square_iff_base : ∀ (g : CSp n F) (m : Fˣ),
    (cspMatrix n F g).transpose * Matrix.J (Fin n) F * cspMatrix n F g =
        (m : F) • Matrix.J (Fin n) F →
      (cspProjection n F g ∈ (pspEmbedding C).range ↔ IsSquare (m : F))

theorem diagonalPCSp_not_base (C : CenterIntersectionSource n F)
    (M : ProjectiveMultiplierSource C) :
    diagonalPCSp O ∉ (pspEmbedding C).range := by
  intro h
  exact O.multiplier_nonsquare
    ((M.square_iff_base (diagonalCSp O) O.multiplier
      (diagonal_transpose_similitude O)).mp h)

end DiagonalMatrices

section ProjectiveCosets

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (O : LiteralDiagonalFieldRealisation n F) (M : ProjectiveMultiplierSource C)

/-- The natural projective action of this actual coset is exactly the
projected FM diagonal automorphism. -/
theorem pcspToAut_diagonal :
    S.pcspToAut (diagonalPCSp O) = projectiveAutHom O.outer.diagonal.unop := by
  apply DFunLike.ext
  intro x
  apply pspEmbedding_injective C
  rw [S.pcspToAut_apply, projective_diagonal_embedding]

include S M in
/-- Index two gives the two actual cosets after the displayed nonsquare
matrix has been shown to lie outside the base image. -/
theorem pcsp_two_cosets (z : PCSp n F) :
    ∃ x : PSp n F, z = pspEmbedding C x ∨ z = pspEmbedding C x * diagonalPCSp O := by
  letI := S.normal_image
  let H := (pspEmbedding C).range
  let q : PCSp n F →* PCSp n F ⧸ H := QuotientGroup.mk' H
  have hd : q (diagonalPCSp O) ≠ 1 := by
    intro h
    exact diagonalPCSp_not_base O C M ((QuotientGroup.eq_one_iff _).mp h)
  obtain ⟨other, hother, honly⟩ :=
    (Nat.card_eq_two_iff' (1 : PCSp n F ⧸ H)).mp S.quotient_card
  by_cases hz : q z = 1
  · obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff z).mp hz
    exact ⟨x, Or.inl hx.symm⟩
  · have heq : q z = q (diagonalPCSp O) :=
      (honly (q z) hz).trans (honly (q (diagonalPCSp O)) hd).symm
    have hm : z * (diagonalPCSp O)⁻¹ ∈ H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (z * (diagonalPCSp O)⁻¹) = 1
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, Or.inr ?_⟩
    rw [hx]
    simp only [mul_assoc, inv_mul_cancel, mul_one]

include S M in
/-- Lift the base element to the actual Sp matrix group through its fixed
surjective central quotient. -/
theorem pcsp_two_cosets_sp (z : PCSp n F) :
    ∃ g : Sp n F, z = pspEmbedding C (spProjection n F g) ∨
      z = pspEmbedding C (spProjection n F g) * diagonalPCSp O := by
  obtain ⟨x, hx⟩ := pcsp_two_cosets S O M z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Sp n F)) x
  exact ⟨g, hx⟩

variable (cover : OddSymplecticFullCoverSource n F)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))

/-- The actual PCSp action lifted through the canonical full-cover map. -/
def pcspToSpAut : PCSp n F →* MulAut (Sp n F) :=
  (projectiveAutEquiv cover L).symm.toMonoidHom.comp S.pcspToAut

@[simp] theorem projective_pcspToSpAut (z : PCSp n F) :
    projectiveAutHom (pcspToSpAut S cover L z) = S.pcspToAut z :=
  (projectiveAutEquiv cover L).apply_symm_apply _

theorem pcspToSpAut_base (g : Sp n F) :
    pcspToSpAut S cover L (pspEmbedding C (spProjection n F g)) = MulAut.conj g := by
  apply (projectiveAutEquiv cover L).injective
  change projectiveAutHom (pcspToSpAut S cover L
    (pspEmbedding C (spProjection n F g))) = projectiveAutHom (MulAut.conj g)
  rw [projective_pcspToSpAut, S.pcspToAut_base, projectiveAutHom_inner]

theorem pcspToSpAut_diagonal : pcspToSpAut S cover L (diagonalPCSp O) =
    O.outer.diagonal.unop := by
  apply (projectiveAutEquiv cover L).injective
  change projectiveAutHom (pcspToSpAut S cover L (diagonalPCSp O)) =
    projectiveAutHom O.outer.diagonal.unop
  rw [projective_pcspToSpAut, pcspToAut_diagonal]

include M in
/-- The group-only two-coset statement is retained as an equality of
ACTUAL Sp automorphisms, with the fixed FM diagonal automorphism. -/
theorem pcspToSpAut_two_forms (z : PCSp n F) :
    ∃ g : Sp n F, pcspToSpAut S cover L z = MulAut.conj g ∨
      pcspToSpAut S cover L z = MulAut.conj g * O.outer.diagonal.unop := by
  obtain ⟨g, hg | hg⟩ := pcsp_two_cosets_sp S O M z
  · refine ⟨g, Or.inl ?_⟩
    rw [hg, pcspToSpAut_base]
  · refine ⟨g, Or.inr ?_⟩
    rw [hg, map_mul, pcspToSpAut_base, pcspToSpAut_diagonal]

section BrauerAction

variable {k K : Type u} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding 2 k K (Sp n F))

/-- Inner invariance here is K class-function invariance, with no source
fixedness premise and no assumption on block labels. -/
theorem inner_op_fixes_ibr (g : Sp n F) (psi : IBr iota) :
    MulOpposite.op (MulAut.conj g) • psi = psi := by
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact PrimeRegularClassFunction.twist_conj psi.1 g

include M in
/-- The resulting character alternatives concern the actual full-cover
lift and the actual opposite-group FM action. They supply no modular
block-triple relation for either alternative. -/
theorem pcsp_ibr_two_actions (z : PCSp n F) (psi : IBr iota) :
    MulOpposite.op (pcspToSpAut S cover L z) • psi = psi ∨
      MulOpposite.op (pcspToSpAut S cover L z) • psi = O.outer.diagonal • psi := by
  obtain ⟨g, hg | hg⟩ := pcspToSpAut_two_forms S O M cover L z
  · left
    rw [hg, inner_op_fixes_ibr]
  · right
    rw [hg, MulOpposite.op_mul, mul_smul, inner_op_fixes_ibr]
    rfl

end BrauerAction
end ProjectiveCosets

end ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
