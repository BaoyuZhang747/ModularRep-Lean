import ModularRep.BrauerCharacterHomPullback
import ModularRep.WeightTransport

/-!
# Literal Brauer extensions under inner normaliser transport

An existing extension is transported along an actual commuting square of group
equivalences. At a conjugate radical, both local groups and both root
conventions are transported by the same inner element, and the field-level
lifts are unchanged. No extension-existence source is introduced.
-/

noncomputable section

namespace Representation.Extension.BrauerCharacterExtensionWitness

open ModularRep

universe u

variable {p : Nat} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]

/-- Transport the actual witness, including its character, through a
commuting square. The root convention is transported, not reselected. -/
def alongEquivalences
    {N : Subgroup G} {M : Subgroup H}
    (eG : G ≃* H) (eN : N ≃* M)
    (hsquare : eG.toMonoidHom.comp N.subtype = M.subtype.comp eN.toMonoidHom)
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (iotaN : PrimeRegularRootEmbedding p k K N) (phiN : IBr iotaN)
    (extension : BrauerCharacterExtensionWitness iotaG iotaN phiN) :
    BrauerCharacterExtensionWitness
      (iotaG.alongMulEquiv eG) (iotaN.alongMulEquiv eN)
      (IrreducibleBrauerCharacter.alongMulEquiv iotaN eN phiN) := by
  refine ⟨IrreducibleBrauerCharacter.alongMulEquiv iotaG eG extension.1, ?_⟩
  apply PrimeRegularClassFunction.ext
  intro x
  have hmap :
      PrimeRegularElement.map eG.symm.toMonoidHom
          (PrimeRegularElement.map M.subtype x) =
        PrimeRegularElement.map N.subtype
          (PrimeRegularElement.map eN.symm.toMonoidHom x) := by
    apply Subtype.ext
    apply eG.injective
    change eG (eG.symm (x.1 : H)) = eG ((eN.symm x.1 : N) : G)
    rw [eG.apply_symm_apply]
    have h := congrArg (fun f : N →* H => f (eN.symm x.1)) hsquare
    change eG ((eN.symm x.1 : N) : G) = (eN (eN.symm x.1) : H) at h
    rw [eN.apply_symm_apply] at h
    exact h.symm
  have hrestriction := congrArg
    (fun f : PrimeRegularClassFunction K N p =>
      f (PrimeRegularElement.map eN.symm.toMonoidHom x)) extension.2
  change extension.1.1
      (PrimeRegularElement.map N.subtype
        (PrimeRegularElement.map eN.symm.toMonoidHom x)) =
    phiN.1 (PrimeRegularElement.map eN.symm.toMonoidHom x) at hrestriction
  exact (congrArg extension.1.1 hmap).trans hrestriction

@[simp]
theorem alongEquivalences_value
    {N : Subgroup G} {M : Subgroup H}
    (eG : G ≃* H) (eN : N ≃* M)
    (hsquare : eG.toMonoidHom.comp N.subtype = M.subtype.comp eN.toMonoidHom)
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (iotaN : PrimeRegularRootEmbedding p k K N) (phiN : IBr iotaN)
    (extension : BrauerCharacterExtensionWitness iotaG iotaN phiN) :
    (alongEquivalences eG eN hsquare iotaG iotaN phiN extension).1.1 =
      PrimeRegularClassFunction.pullback eG.symm.toMonoidHom extension.1.1 := rfl

/-- Transport of an ambient character by an inner automorphism leaves its
actual class function unchanged. This does not assert that all automorphisms
are inner, or identify two independently chosen extensions. -/
theorem inner_transport_value
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (phi : IBr iotaG) (g : G) :
    (IrreducibleBrauerCharacter.alongMulEquiv iotaG (MulAut.conj g) phi).1 =
      phi.1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  have hinv : (MulAut.conj g).symm = MulAut.conj g⁻¹ :=
    (map_inv (MulAut.conj : G →* MulAut G) g).symm
  change phi.1 (PrimeRegularElement.map (MulAut.conj g).symm.toMonoidHom x) = phi.1 x
  rw [hinv]
  exact phi.1.map_conj g⁻¹ x

end Representation.Extension.BrauerCharacterExtensionWitness

namespace ModularRep.InnerNormalizerTransport

universe u

variable {A : Type u} [Group A] [Finite A]

/-- The actual conjugation map, followed only by the proved equality with
the desired literal target radical. -/
def normalizerEquivOfConjEq (Q R : Subgroup A) (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R) :
    Subgroup.normalizer (Q : Set A) ≃* Subgroup.normalizer (R : Set A) :=
  (normalizerEquiv (MulAut.conj a) Q).trans
    (MulEquiv.subgroupCongr
      (congrArg (fun S : Subgroup A => Subgroup.normalizer (S : Set A)) h))

@[simp]
theorem normalizerEquivOfConjEq_coe (Q R : Subgroup A) (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R)
    (n : Subgroup.normalizer (Q : Set A)) :
    (normalizerEquivOfConjEq Q R a h n : A) = a * (n : A) * a⁻¹ := rfl

@[simp]
theorem normalizerEquivOfConjEq_symm_coe (Q R : Subgroup A) (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R)
    (n : Subgroup.normalizer (R : Set A)) :
    ((normalizerEquivOfConjEq Q R a h).symm n : A) = a⁻¹ * (n : A) * a := rfl

/-- Conjugation also transports the literal intersection with the SAME
normal base subgroup. This uses base normality, not base=top. -/
def localBaseEquivOfConjEq (B Q R : Subgroup A) [B.Normal] (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R) :
    B.comap (Subgroup.normalizer (Q : Set A)).subtype ≃*
      B.comap (Subgroup.normalizer (R : Set A)).subtype where
  toFun n := ⟨normalizerEquivOfConjEq Q R a h n.1, by
    change a * (n.1 : A) * a⁻¹ ∈ B
    exact (inferInstance : B.Normal).conj_mem (n.1 : A) n.2 a⟩
  invFun n := ⟨(normalizerEquivOfConjEq Q R a h).symm n.1, by
    change a⁻¹ * (n.1 : A) * a ∈ B
    exact (inferInstance : B.Normal).conj_mem' (n.1 : A) n.2 a⟩
  left_inv n := Subtype.ext ((normalizerEquivOfConjEq Q R a h).symm_apply_apply n.1)
  right_inv n := Subtype.ext ((normalizerEquivOfConjEq Q R a h).apply_symm_apply n.1)
  map_mul' n m := Subtype.ext ((normalizerEquivOfConjEq Q R a h).map_mul n.1 m.1)

theorem localBaseEquivOfConjEq_square (B Q R : Subgroup A) [B.Normal] (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R) :
    (normalizerEquivOfConjEq Q R a h).toMonoidHom.comp
        (B.comap (Subgroup.normalizer (Q : Set A)).subtype).subtype =
      (B.comap (Subgroup.normalizer (R : Set A)).subtype).subtype.comp
        (localBaseEquivOfConjEq B Q R a h).toMonoidHom := by
  ext n
  rfl

/-- The literal intersection normaliser inside an unchanged intermediate J. -/
abbrev IntermediateNormalizer (Q : Subgroup A) (J : Subgroup A) : Subgroup J :=
  (Subgroup.normalizer (Q : Set A)).comap J.subtype

def intermediateInclusion (Q : Subgroup A) (J : Subgroup A) :
    IntermediateNormalizer Q J →* Subgroup.normalizer (Q : Set A) where
  toFun n := ⟨n.1.1, n.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- If the conjugator belongs to J, the global carrier is J on both sides;
only its local normaliser is changed. -/
def intermediateNormalizerEquivOfConjEq (Q R : Subgroup A) (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R)
    (J : Subgroup A) (ha : a ∈ J) :
    IntermediateNormalizer Q J ≃* IntermediateNormalizer R J where
  toFun n := ⟨MulAut.conj (⟨a, ha⟩ : J) n.1, by
    exact (normalizerEquivOfConjEq Q R a h ⟨n.1.1, n.2⟩).2⟩
  invFun n := ⟨(MulAut.conj (⟨a, ha⟩ : J)).symm n.1, by
    exact ((normalizerEquivOfConjEq Q R a h).symm ⟨n.1.1, n.2⟩).2⟩
  left_inv n := Subtype.ext ((MulAut.conj (⟨a, ha⟩ : J)).symm_apply_apply n.1)
  right_inv n := Subtype.ext ((MulAut.conj (⟨a, ha⟩ : J)).apply_symm_apply n.1)
  map_mul' n m := Subtype.ext ((MulAut.conj (⟨a, ha⟩ : J)).map_mul n.1 m.1)

theorem intermediateNormalizerEquivOfConjEq_square
    (Q R : Subgroup A) (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R)
    (J : Subgroup A) (ha : a ∈ J) :
    (MulAut.conj (⟨a, ha⟩ : J)).toMonoidHom.comp
        (IntermediateNormalizer Q J).subtype =
      (IntermediateNormalizer R J).subtype.comp
        (intermediateNormalizerEquivOfConjEq Q R a h J ha).toMonoidHom := by
  ext n
  rfl

theorem intermediateNormalizerEquivOfConjEq_ambient_square
    (Q R : Subgroup A) (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R)
    (J : Subgroup A) (ha : a ∈ J) :
    (normalizerEquivOfConjEq Q R a h).toMonoidHom.comp
        (intermediateInclusion Q J) =
      (intermediateInclusion R J).comp
        (intermediateNormalizerEquivOfConjEq Q R a h J ha).toMonoidHom := by
  ext n
  rfl

variable {p : Nat} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The existing local extension, now on the normaliser of the conjugate
raw radical and its actual normal-base intersection. -/
def localExtensionOfConjEq (B Q R : Subgroup A) [B.Normal] (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R)
    (iotaN : PrimeRegularRootEmbedding p k K (Subgroup.normalizer (Q : Set A)))
    (iotaB : PrimeRegularRootEmbedding p k K
      (B.comap (Subgroup.normalizer (Q : Set A)).subtype))
    (phiB : IBr iotaB)
    (extension : Representation.Extension.BrauerCharacterExtensionWitness
      iotaN iotaB phiB) :
    Representation.Extension.BrauerCharacterExtensionWitness
      (iotaN.alongMulEquiv (normalizerEquivOfConjEq Q R a h))
      (iotaB.alongMulEquiv (localBaseEquivOfConjEq B Q R a h))
      (IrreducibleBrauerCharacter.alongMulEquiv iotaB
        (localBaseEquivOfConjEq B Q R a h) phiB) :=
  Representation.Extension.BrauerCharacterExtensionWitness.alongEquivalences
    (normalizerEquivOfConjEq Q R a h) (localBaseEquivOfConjEq B Q R a h)
    (localBaseEquivOfConjEq_square B Q R a h) iotaN iotaB phiB extension

/-- Both transported roots have exactly their original field-level lifts. -/
theorem localExtensionOfConjEq_root_lifts (B Q R : Subgroup A) [B.Normal] (a : A)
    (h : Q.map (MulAut.conj a).toMonoidHom = R)
    (iotaN : PrimeRegularRootEmbedding p k K (Subgroup.normalizer (Q : Set A)))
    (iotaB : PrimeRegularRootEmbedding p k K
      (B.comap (Subgroup.normalizer (Q : Set A)).subtype)) :
    (iotaN.alongMulEquiv (normalizerEquivOfConjEq Q R a h)).lift = iotaN.lift ∧
    (iotaB.alongMulEquiv (localBaseEquivOfConjEq B Q R a h)).lift = iotaB.lift :=
  ⟨funext (iotaN.alongMulEquiv_lift _), funext (iotaB.alongMulEquiv_lift _)⟩

end ModularRep.InnerNormalizerTransport



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
