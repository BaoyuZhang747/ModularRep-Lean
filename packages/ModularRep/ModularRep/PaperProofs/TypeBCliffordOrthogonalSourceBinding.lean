import ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers
import ModularRep.PaperProofs.TypeBCliffordScalarNorm
import ModularRep.PaperProofs.TypeBCentralKernelSpinBinding

/-!
# The literal Clifford projection and its Spin-to-Omega quotient

The orthogonal projection is the constructed vector conjugation, restricted
to the actual form-preserving subgroup. The finite odd-field source gives
only determinant one, surjectivity of that map to SO, its scalar kernel,
and the norm-square criterion for the actual derived subgroup of SO.

Scalar adjustment proves that Spin maps onto that derived subgroup. The
kernel is proved to be the two scalar signs. Comparing it with the existing
literal Spin-centre order source gives the actual centre as kernel and the
quotient isomorphism. Neither a Spin-image statement nor a quotient
isomorphism nor a representation theoretic target is a source input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding

open TypeBCliffordCarriers TypeBCliffordOrthogonalAction TypeBCliffordScalarNorm

section Projection

variable (n : ℕ) (F : Type) [Field F]

/-- The actual vector action restricted to its proved orthogonal image. -/
def orthogonalProjection : SpecialClifford n F →*
    TypeBOrthogonalOmegaCarriers.Orthogonal n F :=
  TypeBOrthogonalOmegaCarriers.liftToOrthogonal n F (linearAction n F)
    (TypeBCliffordOrthogonalAction.preserves_splitForm n F)

@[simp] theorem orthogonalProjection_value (g : SpecialClifford n F) :
    TypeBOrthogonalOmegaCarriers.orthogonalToLinear n F (orthogonalProjection n F g) =
      linearAction n F g := rfl

/-- SO restriction of that fixed map, with exactly its determinant guard. -/
def projection
    (det_one : ∀ g : SpecialClifford n F,
      TypeBOrthogonalOmegaCarriers.determinant n F (orthogonalProjection n F g) = 1) :
    SpecialClifford n F →* TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F :=
  TypeBOrthogonalOmegaCarriers.liftToSpecialOrthogonal n F
    (orthogonalProjection n F) det_one

@[simp] theorem projection_value
    (det_one : ∀ g : SpecialClifford n F,
      TypeBOrthogonalOmegaCarriers.determinant n F (orthogonalProjection n F g) = 1)
    (g : SpecialClifford n F) :
    TypeBOrthogonalOmegaCarriers.specialOrthogonalToLinear n F
      (projection n F det_one g) = linearAction n F g := rfl

@[simp] theorem projection_scalar
    (det_one : ∀ g : SpecialClifford n F,
      TypeBOrthogonalOmegaCarriers.determinant n F (orthogonalProjection n F g) = 1)
    (z : Fˣ) : projection n F det_one (scalar n F z) = 1 := by
  apply TypeBOrthogonalOmegaCarriers.specialOrthogonalToLinear_injective n F
  change linearAction n F (scalar n F z) = 1
  exact linearAction_scalar n F z

/-- Grove's reversed norm product is the same literal scalar as NormSource.
This comparison uses actual unit cancellation, not a changed norm convention. -/
theorem reverse_norm_value (N : NormSource n F) (g : SpecialClifford n F) :
    CliffordAlgebra.reverse (toClifford n F g) * toClifford n F g =
      algebraMap F (Clifford n F) (N.norm g : F) := by
  have cancel : toClifford n F (g⁻¹) * toClifford n F g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc
    _ = algebraAction n F (g⁻¹)
        (toClifford n F g * CliffordAlgebra.reverse (toClifford n F g)) := by
      rw [algebraAction_apply, inv_inv]
      simp only [← mul_assoc, cancel, one_mul]
    _ = algebraAction n F (g⁻¹) (algebraMap F (Clifford n F) (N.norm g : F)) :=
      congrArg (algebraAction n F (g⁻¹)) (N.value g).symm
    _ = _ := (algebraAction n F (g⁻¹)).commutes (N.norm g : F)

variable (p f : ℕ) [Finite F] [CharP F p]

/-- E1/U: finite odd-field structural facts on the constructed projection.
FLZ Type B, Section 2.5 p.540 and Section 3.1 p.541; independently Grove,
Remarks 2--3 after Corollary 9.9 p.78, Theorem 9.7 p.77 and Proposition
6.14 pp.50--51. The displayed split model and rank ensure the isotropic
nondegenerate scope. No certificate inhabitant is declared. -/
structure Source (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
    (N : NormSource n F) where
  det_one : ∀ g : SpecialClifford n F,
    TypeBOrthogonalOmegaCarriers.determinant n F (orthogonalProjection n F g) = 1
  onto : Function.Surjective (projection n F det_one)
  scalar_kernel : ∀ g : SpecialClifford n F,
    projection n F det_one g = 1 ↔
      ∃ z : Fˣ, toClifford n F g = algebraMap F (Clifford n F) (z : F)
  norm_square_criterion : ∀ g : SpecialClifford n F,
    projection n F det_one g ∈ TypeBOrthogonalOmegaCarriers.omegaSubgroup n F ↔
      ∃ z : Fˣ, N.norm g = z ^ 2

variable {p f}
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n) (N : NormSource n F)
variable (S : Source n F p f parameters rank N)

theorem spin_lands_in_omega (g : Spin n F N) :
    projection n F S.det_one g.val ∈ TypeBOrthogonalOmegaCarriers.omegaSubgroup n F :=
  (S.norm_square_criterion g.val).mpr ⟨1, g.property.trans (one_pow 2).symm⟩

/-- The actual Spin map to the independently defined matrix Omega carrier. -/
def spinProjection : Spin n F N →* TypeBOrthogonalOmegaCarriers.Omega n F :=
  ((projection n F S.det_one).comp (SpinSubgroup n F N).subtype).codRestrict
    (TypeBOrthogonalOmegaCarriers.omegaSubgroup n F)
    (spin_lands_in_omega n F parameters rank N S)

@[simp] theorem spinProjection_value (g : Spin n F N) :
    (spinProjection n F parameters rank N S g).val = projection n F S.det_one g.val := rfl

/-- A lift of an Omega element is adjusted by the inverse scalar square
root of its norm. Surjectivity is proved, not part of the source packet. -/
theorem spinProjection_surjective :
    Function.Surjective (spinProjection n F parameters rank N S) := by
  intro h
  obtain ⟨g, hg⟩ := S.onto h.val
  have homega : projection n F S.det_one g ∈ TypeBOrthogonalOmegaCarriers.omegaSubgroup n F :=
    hg.symm ▸ h.property
  obtain ⟨z, hz⟩ := (S.norm_square_criterion g).mp homega
  refine ⟨⟨scalar n F (z⁻¹) * g, adjusted_mem_spin n F N g z hz⟩, ?_⟩
  apply Subtype.ext
  change projection n F S.det_one (scalar n F (z⁻¹) * g) = h.val
  rw [map_mul, projection_scalar, one_mul, hg]

theorem imageSpin :
    (SpinSubgroup n F N).map (projection n F S.det_one) =
      TypeBOrthogonalOmegaCarriers.omegaSubgroup n F := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact spin_lands_in_omega n F parameters rank N S ⟨g, hg⟩
  · intro hh
    obtain ⟨g, hg⟩ := spinProjection_surjective n F parameters rank N S ⟨h, hh⟩
    exact ⟨g.val, g.property, congrArg Subtype.val hg⟩

end Projection

section Centre

open TypeBCliffordCarriers TypeBCliffordOrthogonalAction TypeBCliffordScalarNorm

variable (n : ℕ) (F : Type) [Field F] (N : NormSource n F)

/-- The scalar -1 is an actual element of the same norm-one subgroup. -/
def minusOneSpin : Spin n F N :=
  ⟨scalar n F (-1), by change N.norm (scalar n F (-1)) = 1; rw [norm_scalar]; simp⟩

theorem minusOneSpin_central :
    minusOneSpin n F N ∈ Subgroup.center (Spin n F N) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (scalar_mem_center n F (-1)) g.val

variable {p f : ℕ} [Finite F] [CharP F p]
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
variable (S : Source n F p f parameters rank N)

include parameters in
theorem minusOneSpin_ne_one : minusOneSpin n F N ≠ 1 := by
  letI : Fact (2 < p) := ⟨parameters.prime.odd_iff.mp parameters.odd⟩
  intro h
  have scalars : scalar n F (-1) = scalar n F 1 :=
    (congrArg Subtype.val h).trans (map_one (scalar n F)).symm
  have units : (-1 : Fˣ) = 1 := scalar_injective n F scalars
  exact CharP.neg_one_ne_one (R := F) p (congrArg (fun z : Fˣ => (z : F)) units)

/-- The kernel consists exactly of the two literal scalar signs. -/
theorem spinProjection_eq_one_iff (g : Spin n F N) :
    spinProjection n F parameters rank N S g = 1 ↔
      g = 1 ∨ g = minusOneSpin n F N := by
  constructor
  · intro h
    have hpi : projection n F S.det_one g.val = 1 := congrArg Subtype.val h
    obtain ⟨z, hz⟩ := (S.scalar_kernel g.val).mp hpi
    have gscalar : g.val = scalar n F z :=
      toClifford_injective n F (hz.trans (toClifford_scalar n F z).symm)
    have square : z ^ 2 = 1 :=
      (norm_scalar n F N z).symm.trans ((congrArg N.norm gscalar).symm.trans g.property)
    have signs : z = 1 ∨ z = -1 := by
      have hs : (z : F) ^ 2 = 1 := congrArg (fun w : Fˣ => (w : F)) square
      rcases sq_eq_one_iff.mp hs with hz1 | hzm
      · exact Or.inl (Units.ext hz1)
      · exact Or.inr (Units.ext hzm)
    rcases signs with rfl | rfl
    · left
      apply Subtype.ext
      exact gscalar.trans (map_one (scalar n F))
    · right
      apply Subtype.ext
      exact gscalar
  · rintro (rfl | rfl)
    · exact map_one _
    · apply Subtype.ext
      exact projection_scalar n F S.det_one (-1)

theorem spin_kernel_le_center :
    (spinProjection n F parameters rank N S).ker ≤ Subgroup.center (Spin n F N) := by
  intro g hg
  rcases (spinProjection_eq_one_iff n F N parameters rank S g).mp hg with rfl | rfl
  · exact (Subgroup.center (Spin n F N)).one_mem
  · exact minusOneSpin_central n F N

/-- Centre order two is used on its actual literal carrier. Its unique
nonidentity element is the already constructed scalar -1, hence central
elements lie in the proved kernel. -/
theorem spin_kernel_eq_center
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N) :
    (spinProjection n F parameters rank N S).ker = Subgroup.center (Spin n F N) := by
  apply le_antisymm (spin_kernel_le_center n F N parameters rank S)
  intro g hg
  by_cases hone : g = 1
  · subst g
    exact map_one _
  · have order := centre.centre_order parameters rank
    obtain ⟨c, _, unique⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center (Spin n F N))).mp order
    let minus : Subgroup.center (Spin n F N) :=
      ⟨minusOneSpin n F N, minusOneSpin_central n F N⟩
    have minus_ne : minus ≠ 1 := by
      intro h
      exact minusOneSpin_ne_one n F N parameters (congrArg Subtype.val h)
    have minus_eq : minus = c := unique minus minus_ne
    have g_eq : (⟨g, hg⟩ : Subgroup.center (Spin n F N)) = c := by
      apply unique
      intro h
      exact hone (congrArg Subtype.val h)
    exact (spinProjection_eq_one_iff n F N parameters rank S g).mpr
      (Or.inr (congrArg Subtype.val (g_eq.trans minus_eq.symm)))

/-- The existing Spin/centre quotient is identified with actual derived SO
by the first isomorphism theorem on the constructed literal projection. -/
def spinQuotientEquiv
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N) :
    (Spin n F N ⧸ Subgroup.center (Spin n F N)) ≃*
      TypeBOrthogonalOmegaCarriers.Omega n F :=
  (QuotientGroup.quotientMulEquivOfEq
    (spin_kernel_eq_center n F N parameters rank S centre).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (spinProjection n F parameters rank N S)
      (spinProjection_surjective n F parameters rank N S))

@[simp] theorem spinQuotientEquiv_mk
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (g : Spin n F N) :
    spinQuotientEquiv n F N parameters rank S centre
        (QuotientGroup.mk' (Subgroup.center (Spin n F N)) g) =
      spinProjection n F parameters rank N S g := rfl

/-- The codomain here is the independently constructed concrete Omega;
the domain is exactly the previously fixed Type B quotient carrier. -/
def matrixOmegaEquiv
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N) :
    TypeBSpinCoverSource.Omega N ≃* TypeBOrthogonalOmegaCarriers.Omega n F :=
  spinQuotientEquiv n F N parameters rank S centre

@[simp] theorem matrixOmegaEquiv_vector
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (g : Spin n F N) (v : Vector n F) :
    TypeBOrthogonalOmegaCarriers.omegaToLinear n F
      (matrixOmegaEquiv n F N parameters rank S centre
        (QuotientGroup.mk' (Subgroup.center (Spin n F N)) g)) v =
      linearAction n F g.val v := rfl

end Centre

end ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
