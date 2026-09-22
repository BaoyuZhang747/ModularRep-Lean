import ModularRep.PaperProofs.TypeBRegularLeviCurrentQuotient
import ModularRep.PaperProofs.TypeBLemma47LeviApplication
import ModularRep.IrreducibleBrauerCharacterEquiv
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Original rational Levi carriers and the finite field actor

Supporting carrier deduction for the actual Levi representative window.
Gamma, H and N are the SAME rational M, L and L0, with canonical subgroup
copies and root transports. No old ambient central decomposition or paired
intersection premise is introduced just to access these carriers.

The quotient proof reuses the accepted current regular-Levi clause (3) and
identifies its literal effective kernel with the characteristic-two API's
H C_Gamma(H). Its exponent is a deduction from the original geometric
centre-order-two source, not an input.

The prescribed cyclic actor E acts only on the finite group of F-fixed
points. Agreement of one generator with the automorphism constructed from
the injective field endomorphism sigma extends chain preservation to E.
No action of E on the algebraic point group, or assertion that sigma has
the same finite order there, is assumed. Algebraic/source interpretation
remains the existing E1 boundary. This helper is not a full window endpoint.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeCarriers

open TypeBRegularLeviRationalCarriers TypeBRegularLeviOrbitLemma46Relative
open TypeBRegularLeviCurrentQuotient TypeBCharacteristicTwoCliffordKernel
open TypeBLemma47LeviApplication
open scoped Pointwise

universe u

variable {A : Type u} [Group A] (Frob : MulAut A) (Lbar : Subgroup A)

abbrev Gamma := M Frob.toMonoidHom Lbar
abbrev H : Subgroup (Gamma Frob Lbar) :=
  (L Frob.toMonoidHom Lbar).subgroupOf (M Frob.toMonoidHom Lbar)
abbrev N : Subgroup (Gamma Frob Lbar) :=
  (L0 Frob.toMonoidHom Lbar).subgroupOf (M Frob.toMonoidHom Lbar)

instance H_normal : (H Frob Lbar).Normal := L_normal_M Frob.toMonoidHom Lbar
instance N_normal : (N Frob Lbar).Normal := L0_normal_M Frob.toMonoidHom Lbar

theorem N_le_H : N Frob Lbar ≤ H Frob Lbar := by
  intro x hx
  exact L0_le_L Frob.toMonoidHom Lbar hx

/-- The original rational L and its literal copy inside Gamma. -/
def originalLEquiv : L Frob.toMonoidHom Lbar ≃* H Frob Lbar where
  toFun x := ⟨⟨x.val, L_le_M Frob.toMonoidHom Lbar x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The original rational L0 and its literal copy inside the SAME Gamma. -/
def originalL0Equiv : L0 Frob.toMonoidHom Lbar ≃* N Frob Lbar where
  toFun x := ⟨⟨x.val, L_le_M Frob.toMonoidHom Lbar
    (L0_le_L Frob.toMonoidHom Lbar x.property)⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem originalLEquiv_value (x : L Frob.toMonoidHom Lbar) :
    (originalLEquiv Frob Lbar x).val.val = x.val := rfl

@[simp] theorem originalL0Equiv_value (x : L0 Frob.toMonoidHom Lbar) :
    (originalL0Equiv Frob Lbar x).val.val = x.val := rfl

theorem quotientN_abelian :
    IsMulCommutative (Gamma Frob Lbar ⧸ N Frob Lbar) :=
  M_quotient_L0_abelian Frob.toMonoidHom Lbar

/-- The centralizer inside Gamma is the inverse image of the original
rational centralizer; L <= M is used for the reverse inclusion. -/
theorem centralizer_eq :
    Subgroup.centralizer (H Frob Lbar : Set (Gamma Frob Lbar)) =
      (Subgroup.centralizer
        (L Frob.toMonoidHom Lbar : Set (fixedPoints Frob.toMonoidHom))).comap
          (M Frob.toMonoidHom Lbar).subtype := by
  ext x
  change x ∈ Subgroup.centralizer (H Frob Lbar : Set (Gamma Frob Lbar)) ↔
    x.val ∈ Subgroup.centralizer
      (L Frob.toMonoidHom Lbar : Set (fixedPoints Frob.toMonoidHom))
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx l hl
    have h := hx ⟨l, L_le_M Frob.toMonoidHom Lbar hl⟩ hl
    exact congrArg Subtype.val h
  · intro hx l hl
    apply Subtype.ext
    exact hx l.val hl

theorem effectiveKernel_eq :
    effectiveConjugationKernel (H Frob Lbar) =
      effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) := by
  unfold effectiveConjugationKernel effectiveKernel
  rw [centralizer_eq]
  rfl

theorem effectiveKernel_exponent_two (Gbar : Subgroup A)
    (levi_le_original : Lbar ≤ Gbar)
    (levi_stable : ∀ a ∈ Lbar, Frob a ∈ Lbar)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2) :
    letI := effectiveConjugationKernel_normal (H Frob Lbar)
    ∀ q : Gamma Frob Lbar ⧸ effectiveConjugationKernel (H Frob Lbar), q ^ 2 = 1 := by
  letI := effectiveConjugationKernel_normal (H Frob Lbar)
  apply quotient_exponent_two_of_squares_mem
  intro x
  rw [effectiveKernel_eq]
  exact square_mem_literal_effectiveKernel Frob Gbar Lbar
    levi_le_original levi_stable centreOrder x

section Roots

variable [Finite (fixedPoints Frob.toMonoidHom)]
variable {ell : ℕ} {k K : Type u} [Field k] [Field K] [CharP k ell]

def rootH (root : PrimeRegularRootEmbedding ell k K (L Frob.toMonoidHom Lbar)) :
    PrimeRegularRootEmbedding ell k K (H Frob Lbar) :=
  root.alongMulEquiv (originalLEquiv Frob Lbar)

def rootN (root : PrimeRegularRootEmbedding ell k K (L0 Frob.toMonoidHom Lbar)) :
    PrimeRegularRootEmbedding ell k K (N Frob Lbar) :=
  root.alongMulEquiv (originalL0Equiv Frob Lbar)

end Roots

section FiniteFieldActor

variable [Finite (fixedPoints Frob.toMonoidHom)]
variable (sigma : A →* A) (injective : Function.Injective sigma)
variable (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
variable (sigma_levi : ∀ a ∈ Lbar, sigma a ∈ Lbar)
variable (sigma_centre : ∀ z ∈ Subgroup.center A, sigma z ∈ Subgroup.center A)
variable {E : Type u} [Group E]
variable (fieldPoints : E →* MulAut (fixedPoints Frob.toMonoidHom))
variable (e0 : E) (generates : Subgroup.zpowers e0 = ⊤)
variable (generatorValue : ∀ x : fixedPoints Frob.toMonoidHom,
  fieldPoints e0 x = fixedPointAutomorphism Frob.toMonoidHom sigma commutes injective x)

include generates in
/-- Preservation extends from the actual specified generator through its
zpowers. No action or finite-order equation on algebraic points is used. -/
theorem map_eq_of_generator (U : Subgroup (fixedPoints Frob.toMonoidHom))
    (atGenerator : U.map (fieldPoints e0).toMonoidHom = U) (e : E) :
    U.map (fieldPoints e).toMonoidHom = U := by
  let stabilizing : Subgroup E :=
    (MulAction.stabilizer (MulAut (fixedPoints Frob.toMonoidHom)) U).comap fieldPoints
  have hg : e0 ∈ stabilizing := by
    change U.map (fieldPoints e0).toMonoidHom = U
    exact atGenerator
  have htop : (⊤ : Subgroup E) ≤ stabilizing := by
    rw [← generates]
    exact Subgroup.zpowers_le.mpr hg
  exact htop (show e ∈ (⊤ : Subgroup E) from trivial)

include sigma injective commutes sigma_levi sigma_centre e0 generates generatorValue in
theorem fieldPoints_preserves_chain (e : E) :
    (L0 Frob.toMonoidHom Lbar).map (fieldPoints e).toMonoidHom = L0 Frob.toMonoidHom Lbar ∧
    (L Frob.toMonoidHom Lbar).map (fieldPoints e).toMonoidHom = L Frob.toMonoidHom Lbar ∧
    (M Frob.toMonoidHom Lbar).map (fieldPoints e).toMonoidHom = M Frob.toMonoidHom Lbar := by
  have hgen : fieldPoints e0 = fixedPointAutomorphism Frob.toMonoidHom sigma commutes injective :=
    MulEquiv.ext generatorValue
  obtain ⟨hN, hH, hG⟩ := endomorphism_preserves_chain Frob.toMonoidHom sigma
    commutes injective Lbar sigma_levi sigma_centre
  refine ⟨map_eq_of_generator Frob fieldPoints e0 generates _ ?_ e,
    map_eq_of_generator Frob fieldPoints e0 generates _ ?_ e,
    map_eq_of_generator Frob fieldPoints e0 generates _ ?_ e⟩
  · simpa only [hgen] using hN
  · simpa only [hgen] using hH
  · simpa only [hgen] using hG

theorem mem_iff_of_map_eq {Q : Type u} [Group Q]
    (U : Subgroup Q) (alpha : MulAut Q) (preserves : U.map alpha.toMonoidHom = U)
    (x : Q) : x ∈ U ↔ alpha x ∈ U := by
  constructor
  · intro hx
    rw [← preserves]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom hx
  · intro hx
    have hmap : alpha x ∈ U.map alpha.toMonoidHom := by simpa only [preserves] using hx
    obtain ⟨y, hy, hxy⟩ := hmap
    exact (alpha.injective hxy) ▸ hy

/-- Restriction of the ORIGINAL actor on fixed points to the actual Gamma. -/
def fieldOnGamma : E →* MulAut (Gamma Frob Lbar) :=
  restrictAutomorphismHom (M Frob.toMonoidHom Lbar) fieldPoints (fun e x =>
    mem_iff_of_map_eq (M Frob.toMonoidHom Lbar) (fieldPoints e)
      (fieldPoints_preserves_chain Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints e0 generates generatorValue e).2.2 x)

@[simp] theorem fieldOnGamma_value (e : E) (x : Gamma Frob Lbar) :
    (fieldOnGamma Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints e0 generates generatorValue e x).val = fieldPoints e x.val := rfl

theorem fieldOnGamma_H_stable (e : E) (x : Gamma Frob Lbar) :
    x ∈ H Frob Lbar ↔
      fieldOnGamma Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints e0 generates generatorValue e x ∈ H Frob Lbar :=
  mem_iff_of_map_eq (L Frob.toMonoidHom Lbar) (fieldPoints e)
    (fieldPoints_preserves_chain Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints e0 generates generatorValue e).2.1 x.val

theorem fieldOnGamma_N_stable (e : E) (x : Gamma Frob Lbar) :
    x ∈ N Frob Lbar ↔
      fieldOnGamma Frob Lbar sigma injective commutes sigma_levi sigma_centre
        fieldPoints e0 generates generatorValue e x ∈ N Frob Lbar :=
  mem_iff_of_map_eq (L0 Frob.toMonoidHom Lbar) (fieldPoints e)
    (fieldPoints_preserves_chain Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints e0 generates generatorValue e).1 x.val

/-- The accepted full clause (3), now with the original cyclic actor and
the exact characteristic-two effective kernel on H <= Gamma. -/
theorem actual_chain_and_field (Gbar : Subgroup A)
    (levi_le_original : Lbar ≤ Gbar)
    (levi_stable : ∀ a ∈ Lbar, Frob a ∈ Lbar)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2) :
    N Frob Lbar ≤ H Frob Lbar ∧
      IsMulCommutative (Gamma Frob Lbar ⧸ N Frob Lbar) ∧
      (letI := effectiveConjugationKernel_normal (H Frob Lbar)
       ∀ q : Gamma Frob Lbar ⧸ effectiveConjugationKernel (H Frob Lbar), q ^ 2 = 1) ∧
      ∀ e,
        (∀ x : Gamma Frob Lbar, x ∈ H Frob Lbar ↔
          fieldOnGamma Frob Lbar sigma injective commutes sigma_levi sigma_centre
            fieldPoints e0 generates generatorValue e x ∈ H Frob Lbar) ∧
        (∀ x : Gamma Frob Lbar, x ∈ N Frob Lbar ↔
          fieldOnGamma Frob Lbar sigma injective commutes sigma_levi sigma_centre
            fieldPoints e0 generates generatorValue e x ∈ N Frob Lbar) := by
  have accepted := regular_levi_clause_three Frob Gbar Lbar levi_le_original levi_stable
    centreOrder sigma injective commutes sigma_levi sigma_centre
  refine ⟨?_, accepted.2.2.2.2.1, effectiveKernel_exponent_two Frob Lbar Gbar
    levi_le_original levi_stable centreOrder, ?_⟩
  · intro x hx
    exact accepted.1 hx
  · intro e
    exact ⟨fieldOnGamma_H_stable Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints e0 generates generatorValue e,
      fieldOnGamma_N_stable Frob Lbar sigma injective commutes sigma_levi sigma_centre
      fieldPoints e0 generates generatorValue e⟩

end FiniteFieldActor

end ModularRep.PaperProofs.TypeBLeviRepresentativeCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
