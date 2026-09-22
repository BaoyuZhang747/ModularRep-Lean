import ModularRep.PaperProofs.TypeBOrthogonalAmbientOmegaBinding
import ModularRep.PaperProofs.TypeBCliffordCentreSource
import ModularRep.PaperProofs.TypeBCriterionHypotheses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv

/-!
# The full natural automorphism map on literal matrix Omega

The fixed Spin projection and the actual Clifford-to-SO ambient projection
give the same automorphism square. The original Clifford kernel and
surjectivity clauses then determine the matrix action. All centralizers
and centres below are subgroups of these fixed carriers.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBMatrixOmegaFullAutomorphismBinding

open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBCliffordOrthogonalSourceBinding TypeBCliffordOrthogonalAmbientQuotient
open TypeBCliffordOrthogonalAmbientActionBinding TypeBOrthogonalAmbientOmegaBinding
open EvenFieldFLZ318FixedTheoremGate

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (S : FieldActionSource n F p f parameters N) (rank : 3 ≤ n)
  (C : Source n F p f parameters rank N)

/-- The kernel is detected on the actual embedded Omega elements. -/
theorem mem_omegaKernel_iff
    (a : OrthogonalAmbient n F parameters rank N C S) :
    a ∈ (omegaAmbientAction S rank C).ker ↔
      ∀ x : Omega n F, a * omegaEmbedding S rank C x =
        omegaEmbedding S rank C x * a := by
  change omegaAmbientAction S rank C a = 1 ↔ _
  constructor
  · intro ha x
    have h := omegaEmbedding_action S rank C a x
    have hx : omegaAmbientAction S rank C a x = x := by
      rw [ha]
      rfl
    rw [hx] at h
    have heq := congrArg
      (fun y : OrthogonalAmbient n F parameters rank N C S => y * a) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
  · intro h
    apply MulEquiv.ext
    intro x
    apply omegaEmbedding_injective S rank C
    change omegaEmbedding S rank C (omegaAmbientAction S rank C a x) =
      omegaEmbedding S rank C x
    rw [omegaEmbedding_action, h x]
    simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Literal conjugation identifies this kernel with the actual centralizer. -/
theorem omegaKernel_eq_centralizer :
    (omegaAmbientAction S rank C).ker =
      Subgroup.centralizer
        (embeddedOmega S rank C : Set (OrthogonalAmbient n F parameters rank N C S)) := by
  ext a
  rw [mem_omegaKernel_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    exact (h y).symm
  · intro h x
    exact (h (omegaEmbedding S rank C x) ⟨x, rfl⟩).symm

/-- The embedded SO centre centralizes the embedded derived SO subgroup. -/
theorem embeddedSOCenter_le_centralizer :
    TypeBCriterionHypotheses.embeddedCenter
        (soFieldAction n F parameters rank N C S) ≤
      Subgroup.centralizer
        (embeddedOmega S rank C : Set (OrthogonalAmbient n F parameters rank N C S)) := by
  rintro _ ⟨z, hz, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨x, rfl⟩
  let j : SpecialOrthogonal n F →* OrthogonalAmbient n F parameters rank N C S :=
    SemidirectProduct.inl
  change j x.val * j z = j z * j x.val
  exact (map_mul j x.val z).symm.trans
    ((congrArg j (Subgroup.mem_center_iff.mp hz x.val)).trans (map_mul j z x.val))

/-- The upstream natural kernel equals the kernel of the same ambient projection. -/
theorem upstream_kernel_eq_projection
    (centreClifford : TypeBCliffordCentreSource.CentreSource n F parameters
      ((by decide : 1 ≤ 3).trans rank))
    (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism S).ker =
      TypeBAutomorphismSource.embeddedCenter S) :
    (TypeBAutomorphismSource.ambientAutomorphism S).ker =
      (ambientProjection n F parameters rank N C S).ker := by
  rw [naturalKernel, ambient_kernel_eq_embeddedScalars]
  change (Subgroup.center (SpecialClifford n F)).map SemidirectProduct.inl =
    (TypeBCliffordScalarNorm.scalar n F).range.map SemidirectProduct.inl
  rw [centreClifford.center_eq_scalarRange]

section FullCover

variable (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
  (fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C))

/-- Automorphisms descend through the literal full Spin projection. -/
def spinOmegaAutEquiv : MulAut (Spin n F N) ≃* MulAut (Omega n F) :=
  SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv.fullCoverAutEquiv
    (spinProjection n F parameters rank N C) fullCover
    (spin_kernel_eq_center n F N parameters rank C centreSpin)

/-- The automorphism equivalence has the prescribed projection value. -/
theorem spinOmegaAutEquiv_apply_projection (alpha : MulAut (Spin n F N))
    (x : Spin n F N) :
    spinOmegaAutEquiv rank C centreSpin fullCover alpha
        (spinProjection n F parameters rank N C x) =
      spinProjection n F parameters rank N C (alpha x) :=
  SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv.fullCoverAutEquiv_apply_q
    (spinProjection n F parameters rank N C) fullCover
    (spin_kernel_eq_center n F N parameters rank C centreSpin) alpha x

/-- Both actual ambient maps give the same automorphism of matrix Omega. -/
theorem ambient_square_apply (a : TypeBWeightStabilizerSource.Ambient S) :
    spinOmegaAutEquiv rank C centreSpin fullCover
        (TypeBAutomorphismSource.ambientAutomorphism S a) =
      omegaAmbientAction S rank C (ambientProjection n F parameters rank N C S a) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := spinProjection_surjective n F parameters rank N C x
  exact (spinOmegaAutEquiv_apply_projection rank C centreSpin fullCover _ g).trans
    (spinProjection_ambient S rank C a g)

/-- Equality of homomorphisms, with the same projection in the lower row. -/
theorem ambient_square :
    (spinOmegaAutEquiv rank C centreSpin fullCover).toMonoidHom.comp
        (TypeBAutomorphismSource.ambientAutomorphism S) =
      (omegaAmbientAction S rank C).comp (ambientProjection n F parameters rank N C S) := by
  apply MonoidHom.ext
  exact ambient_square_apply S rank C centreSpin fullCover

include centreSpin fullCover in
/-- The original natural surjectivity clause transfers through the fixed square. -/
theorem omegaAmbientAction_surjective
    (naturalSurjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism S)) :
    Function.Surjective (omegaAmbientAction S rank C) := by
  intro alpha
  obtain ⟨beta, hbeta⟩ := (spinOmegaAutEquiv rank C centreSpin fullCover).surjective alpha
  obtain ⟨a, rfl⟩ := naturalSurjective beta
  exact ⟨ambientProjection n F parameters rank N C S a,
    (ambient_square_apply S rank C centreSpin fullCover a).symm.trans hbeta⟩

variable (centreClifford : TypeBCliffordCentreSource.CentreSource n F parameters
    ((by decide : 1 ≤ 3).trans rank))
  (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism S).ker =
    TypeBAutomorphismSource.embeddedCenter S)

include centreSpin fullCover centreClifford naturalKernel in
/-- Lifting an element through the actual ambient projection detects its kernel. -/
theorem omegaAmbientAction_ker_eq_bot :
    (omegaAmbientAction S rank C).ker = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  change a = 1
  obtain ⟨b, rfl⟩ := ambientProjection_surjective n F parameters rank N C S a
  have hbeta : spinOmegaAutEquiv rank C centreSpin fullCover
      (TypeBAutomorphismSource.ambientAutomorphism S b) = 1 :=
    (ambient_square_apply S rank C centreSpin fullCover b).trans ha
  have hup : TypeBAutomorphismSource.ambientAutomorphism S b = 1 :=
    (spinOmegaAutEquiv rank C centreSpin fullCover).injective
      (hbeta.trans (map_one (spinOmegaAutEquiv rank C centreSpin fullCover)).symm)
  have hker : b ∈ (ambientProjection n F parameters rank N C S).ker := by
    rw [← upstream_kernel_eq_projection S rank C centreClifford naturalKernel]
    exact hup
  exact hker

include centreSpin fullCover centreClifford naturalKernel in
/-- The literal matrix action is injective. -/
theorem omegaAmbientAction_injective :
    Function.Injective (omegaAmbientAction S rank C) :=
  (omegaAmbientAction S rank C).ker_eq_bot_iff.mp
    (omegaAmbientAction_ker_eq_bot S rank C centreSpin fullCover centreClifford naturalKernel)

include centreSpin fullCover centreClifford naturalKernel in
/-- The full automorphism assertion is a deduction on this precise natural map. -/
theorem omegaAmbientAction_bijective
    (naturalSurjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism S)) :
    Function.Bijective (omegaAmbientAction S rank C) :=
  ⟨omegaAmbientAction_injective S rank C centreSpin fullCover centreClifford naturalKernel,
    omegaAmbientAction_surjective S rank C centreSpin fullCover naturalSurjective⟩

/-- The resulting equivalence has the actual matrix action as its forward map. -/
def omegaAmbientEquiv
    (naturalSurjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism S)) :
    OrthogonalAmbient n F parameters rank N C S ≃* MulAut (Omega n F) :=
  MulEquiv.ofBijective (omegaAmbientAction S rank C)
    (omegaAmbientAction_bijective S rank C centreSpin fullCover centreClifford
      naturalKernel naturalSurjective)

theorem omegaAmbientEquiv_apply
    (naturalSurjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism S))
    (a : OrthogonalAmbient n F parameters rank N C S) :
    omegaAmbientEquiv S rank C centreSpin fullCover centreClifford naturalKernel naturalSurjective a =
      omegaAmbientAction S rank C a := rfl

include centreSpin fullCover centreClifford naturalKernel in
/-- The full ambient centralizer of the embedded Omega is trivial. -/
theorem centralizer_eq_bot :
    Subgroup.centralizer
        (embeddedOmega S rank C : Set (OrthogonalAmbient n F parameters rank N C S)) = ⊥ :=
  (omegaKernel_eq_centralizer S rank C).symm.trans
    (omegaAmbientAction_ker_eq_bot S rank C centreSpin fullCover centreClifford naturalKernel)

include centreSpin fullCover centreClifford naturalKernel in
/-- The actual SO centre is detected by its injective ambient inclusion. -/
theorem soCenter_eq_bot : Subgroup.center (SpecialOrthogonal n F) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  have hmem := embeddedSOCenter_le_centralizer S rank C
    (show SemidirectProduct.inl z ∈ TypeBCriterionHypotheses.embeddedCenter
        (soFieldAction n F parameters rank N C S) from ⟨z, hz, rfl⟩)
  rw [centralizer_eq_bot S rank C centreSpin fullCover centreClifford naturalKernel] at hmem
  have hinl : (SemidirectProduct.inl z : OrthogonalAmbient n F parameters rank N C S) = 1 := hmem
  change z = 1
  exact congrArg SemidirectProduct.left hinl

include centreSpin fullCover centreClifford naturalKernel in
/-- This is the embedded SO centre, not the centre of the whole ambient group. -/
theorem embeddedSOCenter_eq_bot :
    TypeBCriterionHypotheses.embeddedCenter (soFieldAction n F parameters rank N C S) = ⊥ := by
  change (Subgroup.center (SpecialOrthogonal n F)).map SemidirectProduct.inl = ⊥
  rw [soCenter_eq_bot S rank C centreSpin fullCover centreClifford naturalKernel, Subgroup.map_bot]

include centreSpin fullCover centreClifford naturalKernel in
/-- The criterion's centralizer and embedded-centre sides are the same actual subgroups. -/
theorem centralizer_eq_embeddedSOCenter :
    Subgroup.centralizer
        (embeddedOmega S rank C : Set (OrthogonalAmbient n F parameters rank N C S)) =
      TypeBCriterionHypotheses.embeddedCenter (soFieldAction n F parameters rank N C S) :=
  (centralizer_eq_bot S rank C centreSpin fullCover centreClifford naturalKernel).trans
    (embeddedSOCenter_eq_bot S rank C centreSpin fullCover centreClifford naturalKernel).symm

end FullCover

end ModularRep.PaperProofs.TypeBMatrixOmegaFullAutomorphismBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
