import ModularRep.PaperProofs.TypeBCentralKernelInertia
import ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate

/-!
# Canonical inertia-group carriers for the quotient triple theorem

The ambient group of the triple is the actual Brauer inertia T, which need
not be normal in A. The normal base and kernel are their literal comaps to
T; the second ambient group is the raw inertia viewed inside T. Quotient
inertias are identified by the actual projection on every point.
No character, weight, block-triple witness, or source conclusion is assumed
by these carrier identifications.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelTripleCarriers

open TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelBrauerInflation TypeBCentralKernelTripleCertificate

universe u

variable {A : Type u} [Group A]

abbrev inside (S T : Subgroup A) : Subgroup T := S.comap T.subtype

/-- The inclusion into a containing subgroup is fixed pointwise. -/
def insideEquiv (S T : Subgroup A) (hST : S ≤ T) : S ≃* inside S T where
  toFun x := ⟨⟨x.val, hST x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem insideEquiv_val (S T : Subgroup A) (hST : S ≤ T) (x : S) :
    (insideEquiv S T hST x).val.val = x.val := rfl

/-- The two nested encodings of the local intersection have the same
underlying ambient element. -/
def nestedLocalEquiv (G T U : Subgroup A) (hUT : U ≤ T) :
    inside G U ≃* localBase (inside G T) (inside U T) where
  toFun x := ⟨⟨⟨x.val.val, hUT x.val.property⟩, x.val.property⟩, x.property⟩
  invFun x := ⟨⟨x.val.val.val, x.val.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem nestedLocalEquiv_val (G T U : Subgroup A) (hUT : U ≤ T)
    (x : inside G U) :
    (nestedLocalEquiv G T U hUT x).val.val.val = x.val.val := rfl

variable (Z : Subgroup A) [Z.Normal]

/-- The quotient inclusion for an arbitrary subgroup; the subgroup itself
is not required to be normal in A. -/
def subgroupQuotientEmbedding (S : Subgroup A) : QuotientG S Z →* QuotientA Z :=
  QuotientGroup.map (inside Z S) Z S.subtype le_rfl

theorem subgroupQuotientEmbedding_injective (S : Subgroup A) :
    Function.Injective (subgroupQuotientEmbedding Z S) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact (QuotientGroup.ker_map (inside Z S) Z S.subtype le_rfl).trans
    (QuotientGroup.map_mk'_self (inside Z S))

theorem subgroupQuotientEmbedding_range (S : Subgroup A) :
    (subgroupQuotientEmbedding Z S).range = S.map (qA Z) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (inside Z S) x
    exact ⟨s.val, s.property, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨qG S Z ⟨s, hs⟩, rfl⟩

def subgroupImageEquiv (S : Subgroup A) : QuotientG S Z ≃* S.map (qA Z) :=
  (MonoidHom.ofInjective (subgroupQuotientEmbedding_injective Z S)).trans
    (MulEquiv.subgroupCongr (subgroupQuotientEmbedding_range Z S))

/-- Restriction to a full preimage, followed by quotienting its actual
kernel, gives the specified downstairs subgroup, without a normality
assumption on that subgroup. -/
def preimageQuotientEquiv (Sbar : Subgroup (QuotientA Z)) :
    QuotientG (Sbar.comap (qA Z)) Z ≃* Sbar :=
  (subgroupImageEquiv Z (Sbar.comap (qA Z))).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective (qA_surjective Z) Sbar))

@[simp] theorem preimageQuotientEquiv_mk_val (Sbar : Subgroup (QuotientA Z))
    (x : Sbar.comap (qA Z)) :
    (preimageQuotientEquiv Z Sbar (qG _ Z x)).val = qA Z x.val := rfl

def subgroupQuotientEquiv (S : Subgroup A) (Sbar : Subgroup (QuotientA Z))
    (preimage : S = Sbar.comap (qA Z)) : QuotientG S Z ≃* Sbar :=
  (subgroupImageEquiv Z S).trans (MulEquiv.subgroupCongr (by
    change S.map (qA Z) = Sbar
    rw [preimage, Subgroup.map_comap_eq_self_of_surjective (qA_surjective Z)]))

@[simp] theorem subgroupQuotientEquiv_mk_val
    (S : Subgroup A) (Sbar : Subgroup (QuotientA Z))
    (preimage : S = Sbar.comap (qA Z)) (x : S) :
    (subgroupQuotientEquiv Z S Sbar preimage (qG S Z x)).val = qA Z x.val := rfl

theorem kernel_le_preimage (S : Subgroup A) (Sbar : Subgroup (QuotientA Z))
    (preimage : S = Sbar.comap (qA Z)) : Z ≤ S := by
  rw [preimage]
  intro z hz
  change qA Z z ∈ Sbar
  have hzero : qA Z z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  rw [hzero]
  exact Sbar.one_mem

section ActualInertias

variable [Finite A] {p : ℕ} {k K : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  (G : Subgroup A) [G.Normal]
  (hZ : IsPGroup p (kernelInG G Z))
  (root : PrimeRegularRootEmbedding p k K (QuotientG G Z))
  (kernel : Navarro232Principle p k)
  (regular : PrimeRegularQuotientLiftPrinciple.{u} p)

def characterInertiaQuotientEquiv (thetaBar : IBr root) :
    QuotientG (T G (upRoot (kernelInG G Z) hZ root)
      (brauerEquiv (kernelInG G Z) hZ root kernel regular thetaBar)) Z ≃*
      brauerStabilizer (quotientAction G Z) root thetaBar :=
  subgroupQuotientEquiv Z _ _ (brauerStabilizer_quotient G Z hZ root kernel regular thetaBar)

@[simp] theorem characterInertiaQuotientEquiv_mk_val (thetaBar : IBr root)
    (x : T G (upRoot (kernelInG G Z) hZ root)
      (brauerEquiv (kernelInG G Z) hZ root kernel regular thetaBar)) :
    (characterInertiaQuotientEquiv Z G hZ root kernel regular thetaBar (qG _ Z x)).val =
      qA Z x.val := rfl

def rawInertiaQuotientEquiv (W : CharacterWeight p K G) :
    QuotientG (U G W) Z ≃*
      rawStabilizer (quotientAction G Z)
        (TypeBCentralKernelWeightTransport.descend (qG G Z) (qG_surjective G Z)
          (quotientKernelIsPGroup G Z hZ) W) :=
  subgroupQuotientEquiv Z _ _ (rawStabilizer_quotient G Z hZ W)

@[simp] theorem rawInertiaQuotientEquiv_mk_val (W : CharacterWeight p K G) (x : U G W) :
    (rawInertiaQuotientEquiv Z G hZ W (qG _ Z x)).val = qA Z x.val := rfl

include hZ in
theorem kernel_le_rawInertia (W : CharacterWeight p K G) : Z ≤ U G W :=
  kernel_le_preimage Z _ _ (rawStabilizer_quotient G Z hZ W)

end ActualInertias

section TripleInclusions

variable (G T U : Subgroup A) [G.Normal]
  (hZG : Z ≤ G) (hGT : G ≤ T) (hUT : U ≤ T) (hZU : Z ≤ U)

instance insideBaseNormal : (inside G T).Normal := inferInstance
instance insideKernelNormal : (inside Z T).Normal := inferInstance

include hZG in
theorem inside_kernel_le_base : inside Z T ≤ inside G T :=
  Subgroup.comap_mono hZG

include hZU in
theorem inside_kernel_le_local : inside Z T ≤ inside U T :=
  Subgroup.comap_mono hZU

/-- The kernel of the triple quotient is exactly the subgroup used by the
actual inertia quotient, rather than a relabelled abstract copy. -/
theorem inside_kernel_eq : inside Z T = kernelInG T Z := rfl

def tripleBaseEquiv : G ≃* inside G T := insideEquiv G T hGT

def tripleLocalAmbientEquiv : U ≃* inside U T := insideEquiv U T hUT

def tripleLocalBaseEquiv : inside G U ≃* localBase (inside G T) (inside U T) :=
  nestedLocalEquiv G T U hUT

end TripleInclusions

end ModularRep.PaperProofs.TypeBCentralKernelTripleCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
