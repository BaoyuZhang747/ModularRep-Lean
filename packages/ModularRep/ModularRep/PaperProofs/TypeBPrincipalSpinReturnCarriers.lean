import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionSpathSource
import ModularRep.PaperProofs.TypeBMatrixOmegaFullAutomorphismBinding

/-!
# The full-automorphism carrier of the principal Spin return

The map on automorphism ambients uses the same literal Spin projection and
the automorphism equivalence already derived from its universal central
extension property. Its kernel is the Spin centre in the left factor.
The quotient, action and inertia maps retain that point map throughout.
No additional automorphism, perfectness, character or weight source occurs.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalSpinReturnCarriers

open ModularRep TypeBAllRankPrincipalCriterionSpathSource
open TypeBCentralKernelCarriers TypeBCentralKernelTripleCarriers
open TypeBCentralKernelTripleCertificate

section EmbeddedCentre

variable (X : Type) [Group X]

/-- The centre of the base, embedded in its full automorphism ambient. -/
def embeddedCenter : Subgroup (AutAmbient X) :=
  (Subgroup.center X).map (SemidirectProduct.inl : X →* AutAmbient X)

theorem embeddedCenter_le_base : embeddedCenter X ≤ canonicalBase X := by
  rintro _ ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

theorem automorphism_preserves_center (alpha : MulAut X) (x : X)
    (hx : x ∈ Subgroup.center X) : alpha x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := alpha.surjective y
  simpa only [map_mul] using congrArg alpha (Subgroup.mem_center_iff.mp hx y)

instance embeddedCenter_normal : (embeddedCenter X).Normal where
  conj_mem _ hx a := by
    obtain ⟨x, hx, rfl⟩ := hx
    refine ⟨naturalAction X a x,
      automorphism_preserves_center X (naturalAction X a) x hx, ?_⟩
    exact congrArg Subtype.val (baseEquiv_action X a x)

def embeddedCenterEquiv : Subgroup.center X ≃* embeddedCenter X :=
  (Subgroup.center X).equivMapOfInjective
    (SemidirectProduct.inl : X →* AutAmbient X) SemidirectProduct.inl_injective

@[simp] theorem embeddedCenterEquiv_val (x : Subgroup.center X) :
    (embeddedCenterEquiv X x).val = SemidirectProduct.inl x.val := rfl

theorem baseEquiv_mem_kernel (x : X) :
    baseEquiv X x ∈ kernelInG (canonicalBase X) (embeddedCenter X) ↔
      x ∈ Subgroup.center X := by
  change SemidirectProduct.inl x ∈ embeddedCenter X ↔ _
  constructor
  · rintro ⟨z, hz, heq⟩
    exact (SemidirectProduct.inl_injective heq) ▸ hz
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem baseEquiv_center_iff (x : X) :
    baseEquiv X x ∈ Subgroup.center (canonicalBase X) ↔ x ∈ Subgroup.center X := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply (baseEquiv X).injective
    simpa only [map_mul] using h (baseEquiv X y)
  · intro h y
    obtain ⟨y, rfl⟩ := (baseEquiv X).surjective y
    simpa only [map_mul] using congrArg (baseEquiv X) (h y)

theorem kernelInBase_eq_center :
    kernelInG (canonicalBase X) (embeddedCenter X) =
      Subgroup.center (canonicalBase X) := by
  ext x
  obtain ⟨x, rfl⟩ := (baseEquiv X).surjective x
  exact (baseEquiv_mem_kernel X x).trans (baseEquiv_center_iff X x).symm

end EmbeddedCentre

section AmbientMap

variable {X Y : Type} [Group X] [Group Y]
  (q : X →* Y) (rho : MulAut X ≃* MulAut Y)
  (square : ∀ (alpha : MulAut X) (x : X), rho alpha (q x) = q (alpha x))

/-- The two literal coordinate maps with their actual action square. -/
def ambientMap : AutAmbient X →* AutAmbient Y :=
  SemidirectProduct.map q rho.toMonoidHom (by
    intro alpha
    apply MonoidHom.ext
    intro x
    exact (square alpha x).symm)

@[simp] theorem ambientMap_left (a : AutAmbient X) :
    (ambientMap q rho square a).left = q a.left := rfl

@[simp] theorem ambientMap_right (a : AutAmbient X) :
    (ambientMap q rho square a).right = rho a.right := rfl

@[simp] theorem ambientMap_inl (x : X) :
    ambientMap q rho square (SemidirectProduct.inl x) = SemidirectProduct.inl (q x) :=
  SemidirectProduct.map_inl q rho.toMonoidHom _ x

@[simp] theorem ambientMap_inr (alpha : MulAut X) :
    ambientMap q rho square (SemidirectProduct.inr alpha) =
      SemidirectProduct.inr (rho alpha) :=
  SemidirectProduct.map_inr q rho.toMonoidHom _ alpha

theorem ambientMap_surjective (surjective : Function.Surjective q) :
    Function.Surjective (ambientMap q rho square) := by
  intro b
  obtain ⟨x, hx⟩ := surjective b.left
  refine ⟨⟨x, rho.symm b.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact hx
  · exact rho.apply_symm_apply b.right

theorem ambientMap_ker :
    (ambientMap q rho square).ker =
      q.ker.map (SemidirectProduct.inl : X →* AutAmbient X) := by
  ext a
  constructor
  · intro ha
    have hl : q a.left = 1 := congrArg SemidirectProduct.left ha
    have hr : a.right = 1 := rho.injective
      ((congrArg SemidirectProduct.right ha).trans (map_one rho).symm)
    refine ⟨a.left, hl, ?_⟩
    exact SemidirectProduct.ext rfl hr.symm
  · rintro ⟨x, hx, rfl⟩
    change ambientMap q rho square (SemidirectProduct.inl x) = 1
    rw [ambientMap_inl, show q x = 1 from hx, map_one]

theorem ambientMap_ker_center (kernel : q.ker = Subgroup.center X) :
    (ambientMap q rho square).ker = embeddedCenter X := by
  rw [ambientMap_ker, kernel]
  rfl

theorem ambientMap_action (a : AutAmbient X) (x : X) :
    q (naturalAction X a x) = naturalAction Y (ambientMap q rho square a) (q x) := by
  rw [naturalAction_value, naturalAction_value]
  change q (a.left * a.right x * a.left⁻¹) =
    q a.left * rho a.right (q x) * (q a.left)⁻¹
  rw [map_mul, map_mul, map_inv, square]

theorem ambientMap_action_inv (a : AutAmbient X) (x : X) :
    q (naturalAction X a⁻¹ x) =
      naturalAction Y (ambientMap q rho square a)⁻¹ (q x) := by
  rw [← map_inv]
  exact ambientMap_action q rho square a⁻¹ x

theorem canonicalBase_comap :
    (canonicalBase Y).comap (ambientMap q rho square) = canonicalBase X := by
  rw [canonicalBase, canonicalBase,
    SemidirectProduct.range_inl_eq_ker_rightHom,
    SemidirectProduct.range_inl_eq_ker_rightHom]
  ext a
  change rho a.right = 1 ↔ a.right = 1
  constructor
  · intro h
    exact rho.injective (h.trans (map_one rho).symm)
  · intro h
    rw [h, map_one]

end AmbientMap

section QuotientMaps

variable {A B : Type} [Group A] [Group B]

theorem kernel_le_of_comap (f : A →* B) (T : Subgroup A) (Tbar : Subgroup B)
    (preimage : T = Tbar.comap f) : f.ker ≤ T := by
  rw [preimage]
  exact Subgroup.ker_le_comap f Tbar

/-- Inclusion of the same raw inertia lifts through the literal full preimages. -/
theorem inertia_inclusion_of_comaps (f : A →* B)
    (U T : Subgroup A) (Ubar Tbar : Subgroup B)
    (weightPreimage : U = Ubar.comap f) (characterPreimage : T = Tbar.comap f)
    (downstairs : Ubar ≤ Tbar) : U ≤ T := by
  rw [weightPreimage, characterPreimage]
  exact Subgroup.comap_mono downstairs

/-- A first-isomorphism equivalence retaining a specified normal kernel. -/
def quotientEquivOfKer (f : A →* B) (surjective : Function.Surjective f)
    (P : Subgroup A) [P.Normal] (kernel : f.ker = P) : (A ⧸ P) ≃* B :=
  (QuotientGroup.quotientMulEquivOfEq kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f surjective)

@[simp] theorem quotientEquivOfKer_mk (f : A →* B)
    (surjective : Function.Surjective f) (P : Subgroup A) [P.Normal]
    (kernel : f.ker = P) (a : A) :
    quotientEquivOfKer f surjective P kernel (QuotientGroup.mk' P a) = f a := rfl

variable (f : A →* B) (surjective : Function.Surjective f)
  (P : Subgroup A) [P.Normal] (kernel : f.ker = P)
  (T : Subgroup A) (Tbar : Subgroup B)
  (preimage : T = Tbar.comap f)

/-- The map on an actual full-preimage subgroup. -/
def subgroupProjection : T →* Tbar :=
  (f.comp T.subtype).codRestrict Tbar (by
    intro t
    change t.val ∈ Tbar.comap f
    rw [← preimage]
    exact t.property)

@[simp] theorem subgroupProjection_val (t : T) :
    (subgroupProjection f T Tbar preimage t).val = f t.val := rfl

include surjective in
theorem subgroupProjection_surjective :
    Function.Surjective (subgroupProjection f T Tbar preimage) := by
  intro t
  obtain ⟨a, ha⟩ := surjective t.val
  have hmem : a ∈ T := by
    rw [preimage]
    change f a ∈ Tbar
    rw [ha]
    exact t.property
  exact ⟨⟨a, hmem⟩, Subtype.ext ha⟩

include kernel in
theorem subgroupProjection_ker :
    (subgroupProjection f T Tbar preimage).ker = inside P T := by
  ext t
  change subgroupProjection f T Tbar preimage t = 1 ↔ t.val ∈ P
  rw [← kernel]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Quotient of that subgroup by the same ambient kernel. -/
def subgroupQuotientEquiv : (T ⧸ inside P T) ≃* Tbar :=
  quotientEquivOfKer (subgroupProjection f T Tbar preimage)
    (subgroupProjection_surjective f surjective T Tbar preimage)
    (inside P T) (subgroupProjection_ker f P kernel T Tbar preimage)

@[simp] theorem subgroupQuotientEquiv_mk_val (t : T) :
    (subgroupQuotientEquiv f surjective P kernel T Tbar preimage
      (QuotientGroup.mk' (inside P T) t)).val = f t.val := rfl

/-- The same point map identifies every full-preimage subgroup inside the inertia. -/
theorem subgroupQuotient_image (S : Subgroup A) (Sbar : Subgroup B)
    (sourcePreimage : S = Sbar.comap f) :
    ((inside S T).map (QuotientGroup.mk' (inside P T))).map
      (subgroupQuotientEquiv f surjective P kernel T Tbar preimage).toMonoidHom =
        inside Sbar Tbar := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hx
    change (subgroupQuotientEquiv f surjective P kernel T Tbar preimage
      (QuotientGroup.mk' (inside P T) t)).val ∈ Sbar
    rw [subgroupQuotientEquiv_mk_val]
    change t.val ∈ Sbar.comap f
    rw [← sourcePreimage]
    exact ht
  · intro hy
    obtain ⟨x, rfl⟩ :=
      (subgroupQuotientEquiv f surjective P kernel T Tbar preimage).surjective y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (inside P T) x
    refine ⟨QuotientGroup.mk' (inside P T) t, ?_, rfl⟩
    refine ⟨t, ?_, rfl⟩
    change t.val ∈ S
    rw [sourcePreimage]
    change f t.val ∈ Sbar
    change (subgroupQuotientEquiv f surjective P kernel T Tbar preimage
      (QuotientGroup.mk' (inside P T) t)).val ∈ Sbar at hy
    rwa [subgroupQuotientEquiv_mk_val] at hy

def subgroupImageEquiv (S : Subgroup A) (Sbar : Subgroup B)
    (sourcePreimage : S = Sbar.comap f) :
    (inside S T).map (QuotientGroup.mk' (inside P T)) ≃* inside Sbar Tbar :=
  ((subgroupQuotientEquiv f surjective P kernel T Tbar preimage).subgroupMap _).trans
    (MulEquiv.subgroupCongr
      (subgroupQuotient_image f surjective P kernel T Tbar preimage S Sbar sourcePreimage))

@[simp] theorem subgroupImageEquiv_val (S : Subgroup A) (Sbar : Subgroup B)
    (sourcePreimage : S = Sbar.comap f)
    (x : (inside S T).map (QuotientGroup.mk' (inside P T))) :
    (subgroupImageEquiv f surjective P kernel T Tbar preimage S Sbar sourcePreimage x).val =
      subgroupQuotientEquiv f surjective P kernel T Tbar preimage x.val := rfl

end QuotientMaps

section Inertias

variable {X Y k K : Type} [Group X] [Group Y] [Finite X] [Finite Y]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (q : X →* Y) (rho : MulAut X ≃* MulAut Y)
  (square : ∀ (alpha : MulAut X) (x : X), rho alpha (q x) = q (alpha x))
  (rootX : PrimeRegularRootEmbedding 2 k K X)
  (rootY : PrimeRegularRootEmbedding 2 k K Y)
  (theta : IBr rootX) (thetaBar : IBr rootY)
  (values : theta.val = PrimeRegularClassFunction.pullback q thetaBar.val)
  (regular : Function.Surjective (PrimeRegularElement.map (p := 2) q))

include values regular in
/-- Actual character inertia follows from the function-valued inflation equation. -/
theorem characterInertia_comap :
    characterInertia rootX theta =
      (characterInertia rootY thetaBar).comap (ambientMap q rho square) := by
  ext a
  rw [Subgroup.mem_comap, characterInertia_iff, characterInertia_iff]
  have commute : theta.val.twist (naturalAction X a⁻¹) =
      PrimeRegularClassFunction.pullback q
        (thetaBar.val.twist (naturalAction Y (ambientMap q rho square a)⁻¹)) := by
    rw [values]
    apply PrimeRegularClassFunction.ext
    intro x
    change thetaBar.val (PrimeRegularElement.map q
      (PrimeRegularElement.map (naturalAction X a⁻¹).toMonoidHom x)) =
      thetaBar.val (PrimeRegularElement.map
        (naturalAction Y (ambientMap q rho square a)⁻¹).toMonoidHom
        (PrimeRegularElement.map q x))
    exact congrArg thetaBar.val
      (Subtype.ext (ambientMap_action_inv q rho square a x.val))
  constructor
  · intro h
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro y
    obtain ⟨x, rfl⟩ := regular y
    have equality : PrimeRegularClassFunction.pullback q
        (thetaBar.val.twist (naturalAction Y (ambientMap q rho square a)⁻¹)) =
        PrimeRegularClassFunction.pullback q thetaBar.val :=
      commute.symm.trans ((congrArg Subtype.val h).trans values)
    exact congrArg (fun chi : PrimeRegularClassFunction K X 2 => chi x) equality
  · intro h
    apply Subtype.ext
    change theta.val.twist (naturalAction X a⁻¹) = theta.val
    rw [commute, show thetaBar.val.twist
      (naturalAction Y (ambientMap q rho square a)⁻¹) = thetaBar.val from
        congrArg Subtype.val h, ← values]

omit rootX rootY theta thetaBar values regular in
/-- Raw ordinary weights, with the canonical descended ordinary character. -/
theorem weightInertia_comap (surjective : Function.Surjective q)
    (kernelTwo : IsPGroup 2 q.ker) (W : CharacterWeight 2 K X) :
    weightInertia W =
      (weightInertia (TypeBCentralKernelWeightTransport.descend q surjective kernelTwo W)).comap
        (ambientMap q rho square) := by
  ext a
  rw [Subgroup.mem_comap, weightInertia_iff, weightInertia_iff]
  have natural := TypeBCentralKernelWeightTransport.descend_rightTwist
    q surjective kernelTwo (naturalAction X a⁻¹)
    (naturalAction Y (ambientMap q rho square a)⁻¹)
    (ambientMap_action_inv q rho square a) W
  constructor
  · intro h
    rw [← natural, h]
  · intro h
    apply TypeBCentralKernelWeightTransport.descend_injective q surjective kernelTwo
    exact natural.trans h

end Inertias

section Spin

open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  (parameters : OddFieldParameters F p f) (rank : 4 ≤ n) (N : NormSource n F)

abbrev rank3 : 3 ≤ n := Nat.le_trans (by decide : 3 ≤ 4) rank

variable (C : TypeBCliffordOrthogonalSourceBinding.Source
  n F p f parameters (rank3 rank) N)

abbrev q : Spin n F N →* Omega n F :=
  TypeBCliffordOrthogonalSourceBinding.spinProjection n F parameters (rank3 rank) N C

theorem q_surjective : Function.Surjective (q parameters rank N C) :=
  TypeBCliffordOrthogonalSourceBinding.spinProjection_surjective
    n F parameters (rank3 rank) N C

variable (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
  (fullCover : EvenFieldFLZ318FixedTheoremGate.IsUniversalCentralExtension
    (q parameters rank N C))

include centreSpin in
theorem q_ker : (q parameters rank N C).ker = Subgroup.center (Spin n F N) :=
  TypeBCliffordOrthogonalSourceBinding.spin_kernel_eq_center
    n F N parameters (rank3 rank) C centreSpin

def rho : MulAut (Spin n F N) ≃* MulAut (Omega n F) :=
  TypeBMatrixOmegaFullAutomorphismBinding.spinOmegaAutEquiv
    (rank3 rank) C centreSpin fullCover

theorem rho_q (alpha : MulAut (Spin n F N)) (x : Spin n F N) :
    rho parameters rank N C centreSpin fullCover alpha (q parameters rank N C x) =
      q parameters rank N C (alpha x) :=
  TypeBMatrixOmegaFullAutomorphismBinding.spinOmegaAutEquiv_apply_projection
    (rank3 rank) C centreSpin fullCover alpha x

/-- The fixed map between the two full automorphism ambients. -/
def projection : AutAmbient (Spin n F N) →* AutAmbient (Omega n F) :=
  ambientMap (q parameters rank N C) (rho parameters rank N C centreSpin fullCover)
    (rho_q parameters rank N C centreSpin fullCover)

theorem projection_surjective :
    Function.Surjective (projection parameters rank N C centreSpin fullCover) :=
  ambientMap_surjective _ _ _ (q_surjective parameters rank N C)

@[simp] theorem projection_left (a : AutAmbient (Spin n F N)) :
    (projection parameters rank N C centreSpin fullCover a).left =
      q parameters rank N C a.left := rfl

@[simp] theorem projection_right (a : AutAmbient (Spin n F N)) :
    (projection parameters rank N C centreSpin fullCover a).right =
      rho parameters rank N C centreSpin fullCover a.right := rfl

@[simp] theorem projection_inl (x : Spin n F N) :
    projection parameters rank N C centreSpin fullCover (SemidirectProduct.inl x) =
      SemidirectProduct.inl (q parameters rank N C x) := ambientMap_inl _ _ _ x

@[simp] theorem projection_inr (alpha : MulAut (Spin n F N)) :
    projection parameters rank N C centreSpin fullCover (SemidirectProduct.inr alpha) =
      SemidirectProduct.inr (rho parameters rank N C centreSpin fullCover alpha) :=
  ambientMap_inr _ _ _ alpha

abbrev kernel : Subgroup (AutAmbient (Spin n F N)) := embeddedCenter (Spin n F N)

theorem projection_ker :
    (projection parameters rank N C centreSpin fullCover).ker = kernel N :=
  ambientMap_ker_center _ _ _ (q_ker parameters rank N C centreSpin)

theorem kernel_le_base : kernel N ≤ canonicalBase (Spin n F N) :=
  embeddedCenter_le_base (Spin n F N)

include parameters rank centreSpin in
theorem kernel_card : Nat.card (kernel N) = 2 := by
  rw [← Nat.card_congr (embeddedCenterEquiv (Spin n F N)).toEquiv]
  exact centreSpin.centre_order parameters (rank3 rank)

include parameters rank centreSpin in
theorem kernel_isTwoGroup : IsPGroup 2 (kernel N) := by
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using kernel_card parameters rank N centreSpin

include parameters rank centreSpin in
theorem kernelInBase_isTwoGroup :
    IsPGroup 2 (kernelInG (canonicalBase (Spin n F N)) (kernel N)) :=
  (kernel_isTwoGroup parameters rank N centreSpin).comap_subtype

include centreSpin in
theorem q_kernel_isTwoGroup : IsPGroup 2 (q parameters rank N C).ker := by
  rw [q_ker parameters rank N C centreSpin]
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using centreSpin.centre_order parameters (rank3 rank)

def ambientQuotientEquiv :
    (AutAmbient (Spin n F N) ⧸ kernel N) ≃* AutAmbient (Omega n F) :=
  quotientEquivOfKer (projection parameters rank N C centreSpin fullCover)
    (projection_surjective parameters rank N C centreSpin fullCover) (kernel N)
    (projection_ker parameters rank N C centreSpin fullCover)

@[simp] theorem ambientQuotientEquiv_mk (a : AutAmbient (Spin n F N)) :
    ambientQuotientEquiv parameters rank N C centreSpin fullCover
      (QuotientGroup.mk' (kernel N) a) =
      projection parameters rank N C centreSpin fullCover a := rfl

theorem projection_action (a : AutAmbient (Spin n F N)) (x : Spin n F N) :
    q parameters rank N C (naturalAction (Spin n F N) a x) =
      naturalAction (Omega n F) (projection parameters rank N C centreSpin fullCover a)
        (q parameters rank N C x) := ambientMap_action _ _ _ a x

theorem projection_action_inv (a : AutAmbient (Spin n F N)) (x : Spin n F N) :
    q parameters rank N C (naturalAction (Spin n F N) a⁻¹ x) =
      naturalAction (Omega n F) (projection parameters rank N C centreSpin fullCover a)⁻¹
        (q parameters rank N C x) := ambientMap_action_inv _ _ _ a x

theorem base_comap :
    (canonicalBase (Omega n F)).comap
      (projection parameters rank N C centreSpin fullCover) = canonicalBase (Spin n F N) :=
  canonicalBase_comap _ _ _

section ActualInertias

variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Finite (Spin n F N)]

/-- The actual character inertia square, retaining the supplied inflation values. -/
theorem spin_characterInertia_comap
    (root : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (rootOmega : PrimeRegularRootEmbedding 2 k K (Omega n F))
    (theta : IBr root) (thetaOmega : IBr rootOmega)
    (values : theta.val = PrimeRegularClassFunction.pullback
      (q parameters rank N C) thetaOmega.val)
    (regular : Function.Surjective (PrimeRegularElement.map (p := 2)
      (q parameters rank N C))) :
    characterInertia root theta = (characterInertia rootOmega thetaOmega).comap
      (projection parameters rank N C centreSpin fullCover) :=
  characterInertia_comap (q parameters rank N C)
    (rho parameters rank N C centreSpin fullCover)
    (rho_q parameters rank N C centreSpin fullCover)
    root rootOmega theta thetaOmega values regular

/-- Raw Spin inertia descends through the same canonical ordinary-weight map. -/
theorem spin_weightInertia_comap (W : CharacterWeight 2 K (Spin n F N)) :
    weightInertia W = (weightInertia (TypeBCentralKernelWeightTransport.descend
      (q parameters rank N C) (q_surjective parameters rank N C)
      (q_kernel_isTwoGroup parameters rank N C centreSpin) W)).comap
        (projection parameters rank N C centreSpin fullCover) :=
  weightInertia_comap (q parameters rank N C)
    (rho parameters rank N C centreSpin fullCover)
    (rho_q parameters rank N C centreSpin fullCover)
    (q_surjective parameters rank N C)
    (q_kernel_isTwoGroup parameters rank N C centreSpin) W

end ActualInertias

end Spin

end ModularRep.PaperProofs.TypeBPrincipalSpinReturnCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
