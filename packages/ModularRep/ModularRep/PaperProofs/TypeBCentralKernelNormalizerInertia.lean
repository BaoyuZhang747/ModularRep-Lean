import ModularRep.PaperProofs.TypeBCentralKernelInertia
import ModularRep.PaperProofs.TypeBCentralKernelLocalReduction
import ModularRep.IrreducibleBrauerCharacterEquiv

/-!
# Raw-weight inertia and the actual normalizer Brauer inertia

The normalizer and normalizer-quotient automorphisms are induced by the
same ambient conjugation. Reduction of the same defect-zero ordinary
character and literal inflation identify their stabilizers. The only
external inputs used are the previously stated Navarro 3.18 certificate
and prime regular quotient lifts. No stabilizer or triple identity is a
source premise.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelNormalizerInertia

open ModularRep CharacterWeight TypeBCentralKernelCarriers
open TypeBCentralKernelInertia TypeBCentralKernelWeightTransport
open TypeBCentralKernelLocalReduction TypeBCentralKernelBrauerInflation

universe u

variable {p : ℕ} {k K H A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group A]

def normalizerCast {Q R : Subgroup H} (h : Q = R) :
    Subgroup.normalizer (Q : Set H) ≃* Subgroup.normalizer (R : Set H) :=
  MulEquiv.cast (M := fun S : Subgroup H => Subgroup.normalizer (S : Set H)) h

@[simp] theorem normalizerCast_coe {Q R : Subgroup H} (h : Q = R)
    (x : Subgroup.normalizer (Q : Set H)) : (normalizerCast h x : H) = x := by
  subst R
  rfl

theorem quotientCast_mk {Q R : Subgroup H} (h : Q = R)
    (x : Subgroup.normalizer (Q : Set H)) :
    MulEquiv.cast (M := fun S : Subgroup H => NormalizerQuotient S) h
      (localMk Q x) = localMk R (normalizerCast h x) := by
  subst R
  rfl

/-- Actual restriction of alpha to the normalizer of a stable subgroup. -/
def normalizerAut (Q : Subgroup H) (alpha : MulAut H)
    (stable : Q.comap alpha.toMonoidHom = Q) :
    MulAut (Subgroup.normalizer (Q : Set H)) :=
  (normalizerCast stable.symm).trans (rightNormalizerEquiv alpha Q)

@[simp] theorem normalizerAut_coe (Q : Subgroup H) (alpha : MulAut H)
    (stable : Q.comap alpha.toMonoidHom = Q)
    (x : Subgroup.normalizer (Q : Set H)) :
    (normalizerAut Q alpha stable x : H) = alpha x := by
  change alpha (normalizerCast stable.symm x : H) = alpha (x : H)
  exact congrArg alpha (normalizerCast_coe stable.symm x)

/-- The corresponding automorphism of the literal normalizer quotient. -/
def localAut (Q : Subgroup H) (alpha : MulAut H)
    (stable : Q.comap alpha.toMonoidHom = Q) : MulAut (NormalizerQuotient Q) :=
  (MulEquiv.cast (M := fun S : Subgroup H => NormalizerQuotient S)
    stable.symm).trans (rightNormalizerQuotientEquiv alpha Q)

theorem localAut_mk (Q : Subgroup H) (alpha : MulAut H)
    (stable : Q.comap alpha.toMonoidHom = Q)
    (x : Subgroup.normalizer (Q : Set H)) :
    localAut Q alpha stable (localMk Q x) =
      localMk Q (normalizerAut Q alpha stable x) := by
  change rightNormalizerQuotientEquiv alpha Q
    (MulEquiv.cast (M := fun S : Subgroup H => NormalizerQuotient S)
      stable.symm (localMk Q x)) = _
  rw [quotientCast_mk]
  rfl

theorem rightTwist_eq_iff_local_fixed (W : CharacterWeight p K H)
    (alpha : MulAut H) (stable : W.subgroup.comap alpha.toMonoidHom = W.subgroup) :
    W.rightTwist alpha = W ↔
      OrdinaryIrreducibleCharacter.twist K _ W.localCharacter
        (localAut W.subgroup alpha stable) = W.localCharacter := by
  constructor
  · intro h
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro n
    change W.localCharacter (localAut W.subgroup alpha stable (localMk W.subgroup n)) = _
    rw [localAut_mk]
    have hvalue := localCharacter_eq_of_eq h (normalizerCast stable.symm n) n
      (normalizerCast_coe stable.symm n)
    exact (rightTwist_localCharacter W alpha (normalizerCast stable.symm n)).symm.trans hvalue
  · intro h
    apply weight_eq_of_values _ _ stable
    intro x y hxy
    rw [rightTwist_localCharacter]
    have heq : rightNormalizerEquiv alpha W.subgroup x =
        normalizerAut W.subgroup alpha stable y := by
      apply Subtype.ext
      calc
        (rightNormalizerEquiv alpha W.subgroup x : H) = alpha (x : H) := rfl
        _ = alpha (y : H) := congrArg alpha hxy
        _ = (normalizerAut W.subgroup alpha stable y : H) :=
          (normalizerAut_coe W.subgroup alpha stable y).symm
    rw [heq]
    have hvalue := congrArg (fun c : OrdinaryIrreducibleCharacter.Irr K
      (NormalizerQuotient W.subgroup) => c (localMk W.subgroup y)) h
    change W.localCharacter (localAut W.subgroup alpha stable (localMk W.subgroup y)) = _ at hvalue
    rw [localAut_mk] at hvalue
    exact hvalue

/-- Inflation reflects fixedness because every regular quotient element has
a regular normalizer representative. This is function equality, not a
source-supplied inertia assertion. -/
theorem inflated_fixed_iff (W : CharacterWeight p K H)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ) (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (alpha : MulAut H) (stable : W.subgroup.comap alpha.toMonoidHom = W.subgroup) :
    IrreducibleBrauerCharacter.twist (normalizerRoot W iotaQ)
      (inflatedReduction W iotaQ phiQ) (normalizerAut W.subgroup alpha stable) =
        inflatedReduction W iotaQ phiQ ↔
    IrreducibleBrauerCharacter.twist iotaQ phiQ
      (localAut W.subgroup alpha stable) = phiQ := by
  have square (x : PrimeRegularElement
      (G := Subgroup.normalizer (W.subgroup : Set H)) p) :
      PrimeRegularElement.map (localMk W.subgroup)
        (PrimeRegularElement.map (normalizerAut W.subgroup alpha stable).toMonoidHom x) =
      PrimeRegularElement.map (localAut W.subgroup alpha stable).toMonoidHom
        (PrimeRegularElement.map (localMk W.subgroup) x) := by
    apply Subtype.ext
    exact (localAut_mk W.subgroup alpha stable x.val).symm
  constructor
  · intro h
    apply Subtype.ext
    ext x
    obtain ⟨y, rfl⟩ := regular _ (normalizerKernel W) iotaQ.prime
      (normalizerKernel_isPGroup W) x
    have hv := congrArg (fun c : IBr (normalizerRoot W iotaQ) => c.val y) h
    change phiQ.val (PrimeRegularElement.map (localMk W.subgroup)
      (PrimeRegularElement.map (normalizerAut W.subgroup alpha stable).toMonoidHom y)) =
      phiQ.val (PrimeRegularElement.map (localMk W.subgroup) y) at hv
    rw [square] at hv
    exact hv
  · intro h
    apply Subtype.ext
    ext x
    change phiQ.val (PrimeRegularElement.map (localMk W.subgroup)
      (PrimeRegularElement.map (normalizerAut W.subgroup alpha stable).toMonoidHom x)) =
      phiQ.val (PrimeRegularElement.map (localMk W.subgroup) x)
    rw [square]
    exact congrArg (fun c : IBr iotaQ => c.val
      (PrimeRegularElement.map (localMk W.subgroup) x)) h

theorem rightTwist_eq_iff_brauer_fixed [IsAlgClosed K]
    (source : Navarro318Certificate p k K)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (W : CharacterWeight p K H)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ) (reduction : Reduces iotaQ W.localCharacter phiQ)
    (alpha : MulAut H) (stable : W.subgroup.comap alpha.toMonoidHom = W.subgroup) :
    W.rightTwist alpha = W ↔
      IrreducibleBrauerCharacter.twist (normalizerRoot W iotaQ)
        (inflatedReduction W iotaQ phiQ) (normalizerAut W.subgroup alpha stable) =
          inflatedReduction W iotaQ phiQ :=
  (rightTwist_eq_iff_local_fixed W alpha stable).trans
    ((reduction_twist_reflects source iotaQ W.localCharacter W.defectZero phiQ
      reduction (localAut W.subgroup alpha stable)).trans
        (inflated_fixed_iff W iotaQ phiQ regular alpha stable).symm)

section Ambient

variable [Finite A] (G : Subgroup A) [G.Normal]

abbrev ambientNormalizer (Q : Subgroup G) : Subgroup A :=
  Subgroup.normalizer (Q.map G.subtype : Set A)

theorem mem_image_iff (Q : Subgroup G) (g : G) :
    (g : A) ∈ Q.map G.subtype ↔ g ∈ Q := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact (Subtype.ext hxy : x = g) ▸ hx
  · intro h
    exact ⟨g, h, rfl⟩

theorem normalizer_stable (Q : Subgroup G) (a : ambientNormalizer G Q) :
    Q.comap (originalAction G (a : A)).toMonoidHom = Q := by
  ext g
  change originalAction G (a : A) g ∈ Q ↔ g ∈ Q
  have ha := a.property
  rw [Subgroup.mem_normalizer_iff] at ha
  calc
    originalAction G (a : A) g ∈ Q ↔
        (a : A) * (g : A) * (a : A)⁻¹ ∈ Q.map G.subtype :=
      (mem_image_iff G Q (originalAction G (a : A) g)).symm
    _ ↔ (g : A) ∈ Q.map G.subtype := (ha (g : A)).symm
    _ ↔ g ∈ Q := mem_image_iff G Q g

theorem mem_normalizer_of_stable (Q : Subgroup G) (a : A)
    (stable : Q.comap (originalAction G a).toMonoidHom = Q) :
    a ∈ ambientNormalizer G Q := by
  have hm : Q.map (originalAction G a).toMonoidHom = Q := by
    calc
      Q.map (originalAction G a).toMonoidHom =
          (Q.comap (originalAction G a).toMonoidHom).map
            (originalAction G a).toMonoidHom := congrArg _ stable.symm
      _ = Q := Subgroup.map_comap_eq_self_of_surjective (originalAction G a).surjective Q
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have square : (MulAut.conj a).toMonoidHom.comp G.subtype =
      G.subtype.comp (originalAction G a).toMonoidHom := by
    ext g
    rfl
  rw [Subgroup.map_map]
  change Q.map ((MulAut.conj a).toMonoidHom.comp G.subtype) = Q.map G.subtype
  rw [square, ← Subgroup.map_map, hm]

/-- Literal conjugation by N_A(image Q) on N_G(Q). -/
def normalizerAction (Q : Subgroup G) :
    ambientNormalizer G Q →* MulAut (Subgroup.normalizer (Q : Set G)) where
  toFun a := normalizerAut Q (originalAction G (a : A)) (normalizer_stable G Q a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [normalizerAut_coe, Subgroup.coe_one, map_one, MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [MulAut.mul_apply, normalizerAut_coe, Subgroup.coe_mul, map_mul]

@[simp] theorem normalizerAction_coe (Q : Subgroup G)
    (a : ambientNormalizer G Q) (x : Subgroup.normalizer (Q : Set G)) :
    (normalizerAction G Q a x : G) = originalAction G (a : A) x :=
  normalizerAut_coe Q (originalAction G (a : A)) (normalizer_stable G Q a) x

/-- The actual local Brauer inertia as a subgroup of A. -/
def normalizerBrauerInertia (Q : Subgroup G)
    (iotaN : PrimeRegularRootEmbedding p k K (Subgroup.normalizer (Q : Set G)))
    (phiN : IBr iotaN) : Subgroup A :=
  (brauerStabilizer (normalizerAction G Q) iotaN phiN).map
    (ambientNormalizer G Q).subtype

/-- Raw inertia is N_A(Q)_phi for the inflation of the reduction of the
same ordinary local character. Every automorphism uses actual conjugation. -/
theorem raw_inertia_eq_normalizer_brauer [IsAlgClosed K]
    (source : Navarro318Certificate p k K)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (W : CharacterWeight p K G)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ) (reduction : Reduces iotaQ W.localCharacter phiQ) :
    U G W = normalizerBrauerInertia G W.subgroup (normalizerRoot W iotaQ)
      (inflatedReduction W iotaQ phiQ) := by
  ext a
  constructor
  · intro ha
    have hraw := (mem_rawStabilizer (originalAction G) W a).mp ha
    have hs : W.subgroup.comap (originalAction G a⁻¹).toMonoidHom = W.subgroup :=
      congrArg CharacterWeight.subgroup hraw
    have haN : a ∈ ambientNormalizer G W.subgroup := by
      have hi := mem_normalizer_of_stable G W.subgroup a⁻¹ hs
      simpa only [inv_inv] using (ambientNormalizer G W.subgroup).inv_mem hi
    let aN : ambientNormalizer G W.subgroup := ⟨a, haN⟩
    refine ⟨aN, ?_, rfl⟩
    exact (mem_brauerStabilizer (normalizerAction G W.subgroup)
      (normalizerRoot W iotaQ) (inflatedReduction W iotaQ phiQ) aN).mpr
        ((rightTwist_eq_iff_brauer_fixed source regular W iotaQ phiQ reduction
          (originalAction G a⁻¹) (normalizer_stable G W.subgroup aN⁻¹)).mp hraw)
  · rintro ⟨aN, haN, rfl⟩
    rw [mem_rawStabilizer]
    exact (rightTwist_eq_iff_brauer_fixed source regular W iotaQ phiQ reduction
      (originalAction G (aN : A)⁻¹) (normalizer_stable G W.subgroup aN⁻¹)).mpr
        ((mem_brauerStabilizer (normalizerAction G W.subgroup)
          (normalizerRoot W iotaQ) (inflatedReduction W iotaQ phiQ) aN).mp haN)

theorem U_le_ambientNormalizer (W : CharacterWeight p K G) :
    U G W ≤ ambientNormalizer G W.subgroup := by
  intro a ha
  have hraw := (mem_rawStabilizer (originalAction G) W a).mp ha
  have hs : W.subgroup.comap (originalAction G a⁻¹).toMonoidHom = W.subgroup :=
    congrArg CharacterWeight.subgroup hraw
  have hi := mem_normalizer_of_stable G W.subgroup a⁻¹ hs
  simpa only [inv_inv] using (ambientNormalizer G W.subgroup).inv_mem hi

/-- Inclusion into the actual ambient normalizer, derived from raw inertia. -/
def rawNormalizerMap (W : CharacterWeight p K G) :
    U G W →* ambientNormalizer G W.subgroup :=
  Subgroup.inclusion (U_le_ambientNormalizer G W)

/-- The actual normalizer is the local base inside the actual raw inertia.
Both directions preserve the literal ambient A element. -/
def normalizerEquivLocalBase (W : CharacterWeight p K G) :
    Subgroup.normalizer (W.subgroup : Set G) ≃* G.comap (U G W).subtype where
  toFun x := ⟨⟨((x : G) : A), by
    change (x : G) ∈ (U G W).comap G.subtype
    rw [U_comap_base]
    exact x.property⟩, (x : G).property⟩
  invFun x := ⟨⟨(x.val : A), x.property⟩, by
    rw [← U_comap_base G W]
    exact x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem normalizerEquivLocalBase_ambient (W : CharacterWeight p K G)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    ((normalizerEquivLocalBase G W x).val : A) = ((x : G) : A) := rfl

/-- This square binds the nested local carrier's conjugation to the actual
normalizer action used in the inertia theorem. -/
theorem normalizerEquivLocalBase_conjugation (W : CharacterWeight p K G)
    (a : U G W) (x : Subgroup.normalizer (W.subgroup : Set G)) :
    normalizerEquivLocalBase G W
      (normalizerAction G W.subgroup (rawNormalizerMap G W a) x) =
    MulAut.conjNormal (H := G.comap (U G W).subtype) a
      (normalizerEquivLocalBase G W x) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((normalizerAction G W.subgroup (rawNormalizerMap G W a) x : G) : A) =
    (a : A) * ((x : G) : A) * (a : A)⁻¹
  rw [normalizerAction_coe, originalAction_val]
  rfl

def localBaseRoot (W : CharacterWeight p K G)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup)) :
    PrimeRegularRootEmbedding p k K (G.comap (U G W).subtype) :=
  (normalizerRoot W iotaQ).alongMulEquiv (normalizerEquivLocalBase G W)

theorem localBaseRoot_lift (W : CharacterWeight p K G)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (z : k) : (localBaseRoot G W iotaQ).lift z = (normalizerRoot W iotaQ).lift z :=
  (normalizerRoot W iotaQ).alongMulEquiv_lift (normalizerEquivLocalBase G W) z

def localBaseBrauer (W : CharacterWeight p K G)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ) : IBr (localBaseRoot G W iotaQ) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (normalizerRoot W iotaQ)
    (normalizerEquivLocalBase G W) (inflatedReduction W iotaQ phiQ)

theorem localBaseBrauer_value (W : CharacterWeight p K G)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ)
    (x : PrimeRegularElement (G := G.comap (U G W).subtype) p) :
    (localBaseBrauer G W iotaQ phiQ).val x =
      (inflatedReduction W iotaQ phiQ).val
        (PrimeRegularElement.map (normalizerEquivLocalBase G W).symm.toMonoidHom x) := rfl

theorem localBaseBrauer_reduction (W : CharacterWeight p K G)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ) (reduction : Reduces iotaQ W.localCharacter phiQ)
    (x : PrimeRegularElement (G := G.comap (U G W).subtype) p) :
    W.localCharacter (localMk W.subgroup ((normalizerEquivLocalBase G W).symm x.val)) =
      (localBaseBrauer G W iotaQ phiQ).val x :=
  inflatedReduction_value W iotaQ phiQ reduction
    (PrimeRegularElement.map (normalizerEquivLocalBase G W).symm.toMonoidHom x)

/-- The transported character is invariant under the actual raw inertia's
conjugation on its local base, as required for literal triple carriers. -/
theorem localBaseBrauer_fixed [IsAlgClosed K]
    (source : Navarro318Certificate p k K)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (W : CharacterWeight p K G)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ) (reduction : Reduces iotaQ W.localCharacter phiQ)
    (a : U G W) :
    IrreducibleBrauerCharacter.twist (localBaseRoot G W iotaQ)
      (localBaseBrauer G W iotaQ phiQ)
      (MulAut.conjNormal (H := G.comap (U G W).subtype) a) =
        localBaseBrauer G W iotaQ phiQ := by
  let e := normalizerEquivLocalBase G W
  let alpha := normalizerAction G W.subgroup (rawNormalizerMap G W a)
  have ha : W.rightTwist (originalAction G (a : A)) = W := by
    have hi := (mem_rawStabilizer (originalAction G) W ((a : A)⁻¹)).mp a⁻¹.property
    simpa only [inv_inv] using hi
  have fixed : IrreducibleBrauerCharacter.twist (normalizerRoot W iotaQ)
      (inflatedReduction W iotaQ phiQ) alpha = inflatedReduction W iotaQ phiQ :=
    (rightTwist_eq_iff_brauer_fixed source regular W iotaQ phiQ reduction
      (originalAction G (a : A))
      (normalizer_stable G W.subgroup (rawNormalizerMap G W a))).mp ha
  have conjugation : MulAut.congr e alpha =
      MulAut.conjNormal (H := G.comap (U G W).subtype) a := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    change e (alpha (e.symm (e y))) = _
    rw [e.symm_apply_apply]
    exact normalizerEquivLocalBase_conjugation G W a y
  have natural := IrreducibleBrauerCharacter.equivAlongMulEquiv_twist
    (normalizerRoot W iotaQ) e (inflatedReduction W iotaQ phiQ) alpha
  rw [fixed, conjugation] at natural
  exact natural.symm

end Ambient

end ModularRep.PaperProofs.TypeBCentralKernelNormalizerInertia


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
