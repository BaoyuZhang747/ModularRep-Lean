import ManuscriptIBAW.TypeC.OddRationalSeries
import ModularRep.PaperProofs.TypeBOrthogonalFieldAutomorphism
import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding
import ModularRep.PaperProofs.TypeBSpinInnerClassActions
import ModularRep.PaperProofs.TypeCCurrentConstituentFactorization

/-!
# Automorphisms of rational series in Lemma 3.12

Taylor's Proposition 7.2 transports an ordinary character by inverse
pullback and its rational semisimple label by the inverse dual isogeny. The
dual field map here is the coordinate automorphism of the specified special
orthogonal group. The source interpretation identifies it with the algebraic
dual field isogeny using the torus and root convention of Section 6.5.

The regular embedding source gives the restriction formula through the
constructed projection from GSpin to SO. Reindexing the finite scalar
product proves diagonal stability. Taylor's formula and preservation of
element orders prove field stability. These arguments derive stability of
the rational ℓ′ union from ordinary character statements.
-/

noncomputable section
open scoped MonoidAlgebra BigOperators
namespace ManuscriptIBAW.TypeC.OddRationalAutomorphisms
open ModularRep ModularRep.PaperProofs OrdinaryIrreducibleCharacter
open TypeCOddPrimeConformalCriterionCarriers
open OddTwoConformalProjectiveRealisation (CSp)
open TypeBOrthogonalOmegaCarriers TypeBOrthogonalFieldAutomorphism
open OddGFactorizationLemma312Relative TypeBCriterionHypotheses
open TypeCCurrentConstituentFactorization (combinedAut combinedAut_eq)

section Restriction
variable {M : Type} [Group M] [Finite M] (G : Subgroup M) [G.Normal]

local instance restrictionFintype : Fintype G := Fintype.ofFinite _

/-- Occurrence in ordinary restriction, tested by the complex scalar product. -/
def occurs (Phi : Irr ℂ M) (chi : Irr ℂ G) : Prop :=
  (Nat.card G : ℂ)⁻¹ * ∑ x : G, chi x⁻¹ * Phi x.val ≠ 0

/-- Conjugation by the ambient group fixes the restricted character and
preserves its nonzero constituent scalar products. No rational series
assumption is needed. -/
theorem occurs_diagonal (Phi : Irr ℂ M) (chi : Irr ℂ G) (m : M) :
    occurs G Phi (twist ℂ G chi (MulAut.conjNormal (H := G) m⁻¹)) ↔
      occurs G Phi chi := by
  classical
  let beta := MulAut.conjNormal (H := G) m⁻¹
  have hPhi (x : G) : Phi (beta x).val = Phi x.val :=
    congrArg (fun theta : Irr ℂ M => theta x.val)
      (TypeBSpinInnerClassActions.ordinaryTwist_inner Phi m⁻¹)
  have hsum : (∑ x : G, chi (beta x⁻¹) * Phi x.val) =
      ∑ x : G, chi x⁻¹ * Phi x.val := by
    calc
      _ = ∑ x : G, chi (beta x)⁻¹ * Phi (beta x).val := by
        apply Finset.sum_congr rfl
        intro x _
        rw [map_inv, hPhi]
      _ = _ := beta.toEquiv.sum_comp (fun x : G => chi x⁻¹ * Phi x.val)
  change (Nat.card G : ℂ)⁻¹ * (∑ x : G, chi (beta x⁻¹) * Phi x.val) ≠ 0 ↔ _
  rw [hsum]
  rfl
end Restriction

variable (n : ℕ) (F : Type) [Field F] [Finite F]
  [(SpSubgroup n F).Normal]
  {K : Type} [Field K] [CharZero K]
  (upper : OddRationalSeries.Conformal n F K)
  (lower : OddRationalSeries.Symplectic n F K)
  (scope : StructuralSource n F)

/-- Cabanes–Enguehard, Proposition 15.6(i), with its interpretation of rational
lifts in the dual group, for the specified upper and lower rational series.
The determinant equation restricts the constructed vector conjugation
projection to SO. The scalar product tests occurrence as an ordinary
constituent. -/
structure RegularEmbeddingSource (scope : StructuralSource n F) : Prop where
  determinant_one : ∀ g : TypeBCliffordCarriers.SpecialClifford n F,
    determinant n F (TypeBCliffordOrthogonalSourceBinding.orthogonalProjection n F g) = 1
  semisimple_lift : ∀ s : SpecialOrthogonal n F, (orderOf s).Coprime (Nat.card F) →
    ∃ t : TypeBCliffordCarriers.SpecialClifford n F,
      (orderOf t).Coprime (Nat.card F) ∧
      TypeBCliffordOrthogonalSourceBinding.projection n F determinant_one t = s
  restriction : ∀ (t : TypeBCliffordCarriers.SpecialClifford n F),
    (orderOf t).Coprime (Nat.card F) → ∀ chi : Irr ℂ (SpSubgroup n F),
    lower.rational chi (TypeBCliffordOrthogonalSourceBinding.projection n F determinant_one t) ↔
      ∃ Phi : Irr ℂ (CSp n F), upper.rational Phi t ∧ occurs (SpSubgroup n F) Phi chi

/-- Taylor, Proposition 7.2, with the identification of the algebraic dual field
isogeny and the torus and root convention of Section 6.5 for the specified
Sp and SO models. The character is chi composed with the inverse of e. Its
label is transported by the inverse of the specified dual coordinate map.
This source concerns ordinary characters only. -/
structure Taylor72Source (scope : StructuralSource n F) : Prop where
  transport : ∀ (e : F ≃+* F) (chi : Irr ℂ (SpSubgroup n F))
      (s : SpecialOrthogonal n F), lower.rational chi s →
    lower.rational (twist ℂ (SpSubgroup n F) chi (spFieldAction n F e⁻¹))
      ((specialOrthogonalAutomorphism n F e).symm s)

variable (regular : RegularEmbeddingSource n F upper lower scope)
  (taylor : Taylor72Source n F lower scope)

include regular in
/-- The restriction formula implies diagonal stability of each rational series. -/
theorem rational_diagonal (m : CSp n F) (chi : Irr ℂ (SpSubgroup n F))
    (s : SpecialOrthogonal n F) (h : lower.rational chi s) :
    lower.rational (twist ℂ (SpSubgroup n F) chi
      (MulAut.conjNormal (H := SpSubgroup n F) m⁻¹)) s := by
  obtain ⟨t, ht, hproj⟩ := regular.semisimple_lift s (lower.semisimple chi s h)
  obtain ⟨Phi, hPhi, hoccurs⟩ := (regular.restriction t ht chi).mp (hproj.symm ▸ h)
  rw [← hproj]
  exact (regular.restriction t ht _).mpr
    ⟨Phi, hPhi, (occurs_diagonal (SpSubgroup n F) Phi chi m).mpr hoccurs⟩

include regular in
/-- Diagonal stability of the rational ℓ′ union follows for every ell. -/
theorem ellPrime_diagonal (ell : ℕ) (m : CSp n F) (chi : Irr K (SpSubgroup n F))
    (h : lower.ellPrime ell chi) :
    lower.ellPrime ell (twist K (SpSubgroup n F) chi
      (MulAut.conjNormal (H := SpSubgroup n F) m⁻¹)) := by
  obtain ⟨s, hs, hell, hchi⟩ := h
  refine ⟨s, hs, hell, ?_⟩
  rw [lower.complexCharacter_twist]
  exact rational_diagonal n F upper lower scope regular m _ s hchi

include taylor in
/-- The inverse dual field map preserves element orders. Taylor's ordinary
series formula therefore preserves the rational ℓ′ union. -/
theorem ellPrime_field (ell : ℕ) (e : F ≃+* F) (chi : Irr K (SpSubgroup n F))
    (h : lower.ellPrime ell chi) :
    lower.ellPrime ell (twist K (SpSubgroup n F) chi (spFieldAction n F e⁻¹)) := by
  obtain ⟨s, hs, hell, hchi⟩ := h
  let dual := (specialOrthogonalAutomorphism n F e).symm
  refine ⟨dual s, ?_, ?_, ?_⟩
  · simpa only [dual.orderOf_eq] using hs
  · simpa only [dual.orderOf_eq] using hell
  · rw [lower.complexCharacter_twist]
    exact taylor.transport e _ s hchi

include regular taylor in
/-- The two ordinary source statements give stability under the conformal group
and field automorphisms, as required by the global Conlon construction. -/
theorem ellPrime_ambient (ell : ℕ) (a : Ambient (fieldAction n F))
    (chi : Irr K (SpSubgroup n F)) (h : lower.ellPrime ell chi) :
    lower.ellPrime ell (ordinaryAutomorphismAct
      (combinedAut (SpSubgroup n F) (fieldAction n F) (naturalAction n F)) a chi) := by
  rw [combinedAut_eq]
  letI : MulAction (Ambient (fieldAction n F)) (Irr K (SpSubgroup n F)) :=
    OrdinaryAction.rightAutomorphismAction (naturalAction n F).hom
  change lower.ellPrime ell (a • chi)
  rw [← SemidirectProduct.inl_left_mul_inr_right a, mul_smul]
  have hf : lower.ellPrime ell
      ((SemidirectProduct.inr a.right : Ambient (fieldAction n F)) • chi) := by
    change lower.ellPrime ell (twist K (SpSubgroup n F) chi
      (ambientAutomorphism n F (SemidirectProduct.inr a.right)⁻¹))
    simp only [← map_inv, ambientAutomorphism_inr]
    exact ellPrime_field n F lower scope taylor ell a.right chi h
  change lower.ellPrime ell (twist K (SpSubgroup n F)
    ((SemidirectProduct.inr a.right : Ambient (fieldAction n F)) • chi)
    (ambientAutomorphism n F (SemidirectProduct.inl a.left)⁻¹))
  simp only [← map_inv, ambientAutomorphism_inl]
  exact ellPrime_diagonal n F upper lower scope regular ell a.left _ hf

end ManuscriptIBAW.TypeC.OddRationalAutomorphisms

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
