import ManuscriptIBAW.TypeC.PrincipalConverse
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Centralisers of the independent surviving products

The scalar centraliser calculation for each basic summand is assumed in the
form given below. A direct matrix argument proves that commuting with the
independent central signs preserves those summands. The product centraliser
calculation and the product being a 2-group are proved here.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer
open ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin
open ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource

universe u

variable {n : ℕ} {F : Type u} [Field F] [Fintype F]

local instance productSpFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

/-- The negative identity matrix on a symplectic summand. -/
def negativeIdentity (r : ℕ) : Sp r F :=
  ⟨-1, SymplecticGroup.neg_mem (one_mem (Matrix.symplecticGroup (Fin r) F))⟩

variable (P : ProductShape n F) (A : P.Geometry)

/-- One independently chosen block, with identity on every other summand. -/
def singleBlock (c : P.Copy) (x : Sp (P.rank c.1) F) : P.BlockGroups := by
  classical
  exact Function.update (fun _ => 1) c x

@[simp] theorem singleBlock_apply_same (c : P.Copy) (x : Sp (P.rank c.1) F) :
    singleBlock P c x c = x := by
  classical
  simp [singleBlock]

theorem singleBlock_mem (c : P.Copy) (x : Sp (P.rank c.1) F)
    (hx : x ∈ (P.basic c.1).subgroup) :
    A.embedding (singleBlock P c x) ∈ A.subgroup := by
  classical
  apply (A.mem_subgroup _).mpr
  refine ⟨singleBlock P c x, ?_, rfl⟩
  intro d
  by_cases h : d = c
  · subst d
    simpa using hx
  · simp [singleBlock, Function.update_of_ne h]

/-- The direct sum statement for the matrices in `Geometry`. The following
theorem proves it from the specified matrix equations. -/
structure IndependentSignSeparation : Prop where
  preserves_summands : Odd (Nat.card F) → ∀ x : Sp n F,
    (∀ c : P.Copy, Commute x
      (A.embedding (singleBlock P c (negativeIdentity (F := F) (P.rank c.1))))) →
    ∃ g : P.BlockGroups, A.embedding g = x

/-- Commutation with each independent sign makes every matrix entry between
distinct summands zero. The symplectic equation restricts to each diagonal
block, giving an element of the specified block diagonal group. -/
theorem independentSignSeparation : IndependentSignSeparation P A where
  preserves_summands fieldOdd x commutes := by
    classical
    let : DecidableEq P.Copy := P.copyDecidableEq
    let : DecidableEq P.Coordinates := P.coordinatesDecidableEq
    let e := Matrix.reindexRingEquiv F A.basisIndex
    let M := e.symm (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    let B := fun c : P.Copy => M.submatrix (Sigma.mk c) (Sigma.mk c)
    have hsign (c : P.Copy) :
        e.symm (A.embedding (singleBlock P c
          (negativeIdentity (F := F) (P.rank c.1))) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          Matrix.diagonal (fun a : P.Coordinates => if a.1 = c then -1 else 1) := by
      rw [A.embedding_matrix]
      change e.symm (e _) = _
      rw [e.symm_apply_apply]
      have hlocal : (fun d : P.Copy =>
          ((singleBlock P c (negativeIdentity (F := F) (P.rank c.1))) d :
            Matrix (Fin (P.rank d.1) ⊕ Fin (P.rank d.1))
              (Fin (P.rank d.1) ⊕ Fin (P.rank d.1)) F)) =
          (fun d : P.Copy => Matrix.diagonal
            (fun _ : Fin (P.rank d.1) ⊕ Fin (P.rank d.1) =>
              if d = c then (-1 : F) else 1)) := by
        funext d
        by_cases hd : d = c
        · subst d
          ext i j
          by_cases hij : i = j <;>
            simp [singleBlock, negativeIdentity, Matrix.diagonal, hij]
        · simp [singleBlock, hd]
      rw [hlocal, Matrix.blockDiagonal'_diagonal]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
    have hoff : ∀ (c d : P.Copy), c ≠ d →
        ∀ i j, M ⟨c, i⟩ ⟨d, j⟩ = 0 := by
      intro c d hcd i j
      have hm := congrArg (fun z : Sp n F =>
        e.symm (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
          (commutes c).eq
      change e.symm (_ * _) = e.symm (_ * _) at hm
      rw [map_mul, map_mul, hsign] at hm
      have hv := congrArg (fun z : Matrix P.Coordinates P.Coordinates F =>
        z ⟨c, i⟩ ⟨d, j⟩) hm
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, if_neg hcd.symm,
        if_true, mul_one, neg_one_mul] at hv
      have htwo := ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion.two_ne_zero_of_odd_card
        fieldOdd
      apply (mul_eq_zero.mp (show (2 : F) * M ⟨c, i⟩ ⟨d, j⟩ = 0 by
        change M ⟨c, i⟩ ⟨d, j⟩ = -M ⟨c, i⟩ ⟨d, j⟩ at hv
        linear_combination hv)).resolve_left htwo
    have hM : M = Matrix.blockDiagonal' B := by
      ext ⟨c, i⟩ ⟨d, j⟩
      by_cases hcd : c = d
      · subst d
        simp [B]
      · rw [Matrix.blockDiagonal'_apply_ne B i j hcd]
        exact hoff c d hcd i j
    have hform : M * Matrix.blockDiagonal'
          (fun c : P.Copy => Matrix.J (Fin (P.rank c.1)) F) * M.transpose =
        Matrix.blockDiagonal' (fun c : P.Copy => Matrix.J (Fin (P.rank c.1)) F) := by
      have hx := congrArg e.symm (SymplecticGroup.mem_iff.mp x.2)
      rw [map_mul, map_mul, ← A.gram_equation] at hx
      change M * e.symm (e _) * M.transpose = e.symm (e _) at hx
      simpa only [e.symm_apply_apply] using hx
    have hB (c : P.Copy) : B c ∈ Matrix.symplecticGroup (Fin (P.rank c.1)) F := by
      apply SymplecticGroup.mem_iff.mpr
      rw [hM, Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul,
        ← Matrix.blockDiagonal'_mul] at hform
      have h := congrArg (fun z : Matrix P.Coordinates P.Coordinates F =>
        z.submatrix (Sigma.mk c) (Sigma.mk c)) hform
      ext i j
      simpa only [Matrix.submatrix_apply, Matrix.blockDiagonal'_apply_eq] using
        congrFun (congrFun h i) j
    refine ⟨fun c => ⟨B c, hB c⟩, ?_⟩
    apply Subtype.ext
    rw [A.embedding_matrix]
    change e (Matrix.blockDiagonal' B) = _
    rw [← hM]
    exact e.apply_symm_apply _

/-- The local portion of An, p. 198, for the actual surviving basic subgroups,
including their wreath extensions. Each centraliser consists of the two
scalar signs, and both signs lie in the basic subgroup. -/
structure AnBasicCentralizers : Prop where
  is_two_group : ∀ i, IsPGroup 2 (P.basic i).subgroup
  negative_mem : ∀ i, negativeIdentity (F := F) (P.rank i) ∈ (P.basic i).subgroup
  centralizer_scalar : ∀ i, ∀ x : Sp (P.rank i) F,
    x ∈ Subgroup.centralizer ((P.basic i).subgroup : Set (Sp (P.rank i) F)) →
    x = 1 ∨ x = negativeIdentity (F := F) (P.rank i)

theorem independentProduct_isPGroup (S : AnBasicCentralizers P) :
    IsPGroup 2 A.subgroup := by
  classical
  have hBlocks : IsPGroup 2 P.independentBlocks := by
    intro g
    have hg : ∀ c : P.Copy, g.1 c ∈ (P.basic c.1).subgroup := by
      simpa [ProductShape.independentBlocks, Subgroup.mem_pi] using g.2
    have hlocal : ∀ c : P.Copy, ∃ e : ℕ, (g.1 c) ^ 2 ^ e = 1 := by
      intro c
      obtain ⟨e, he⟩ := S.is_two_group c.1 ⟨g.1 c, hg c⟩
      exact ⟨e, congrArg Subtype.val he⟩
    choose exponent hexponent using hlocal
    refine ⟨∑ c, exponent c, ?_⟩
    apply Subtype.ext
    funext c
    have hle : exponent c ≤ ∑ d, exponent d :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr (hexponent c)).trans (pow_dvd_pow 2 hle))
  exact hBlocks.map A.embedding

/-- Independent central signs force a centralizing element into the block
diagonal group. Its individual blocks centralize the corresponding basic
subgroups and therefore are scalar signs belonging to those subgroups. -/
theorem independentProduct_centralizer_le (fieldOdd : Odd (Nat.card F))
    (L : IndependentSignSeparation P A) (S : AnBasicCentralizers P) :
    Subgroup.centralizer (A.subgroup : Set (Sp n F)) ≤ A.subgroup := by
  intro x hx
  have hsign : ∀ c : P.Copy, Commute x
      (A.embedding (singleBlock P c (negativeIdentity (F := F) (P.rank c.1)))) := by
    intro c
    exact (hx _ (singleBlock_mem P A c _ (S.negative_mem c.1))).symm
  obtain ⟨g, hg⟩ := L.preserves_summands fieldOdd x hsign
  apply (A.mem_subgroup x).mpr
  refine ⟨g, ?_, hg⟩
  intro c
  have hc : g c ∈ Subgroup.centralizer
      ((P.basic c.1).subgroup : Set (Sp (P.rank c.1) F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxy := hx _ (singleBlock_mem P A c y hy)
    rw [← hg, ← map_mul, ← map_mul] at hxy
    have h := congrArg (fun a : P.BlockGroups => a c) (A.embedding_injective hxy)
    simpa using h
  rcases S.centralizer_scalar c.1 (g c) hc with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact S.negative_mem c.1

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
