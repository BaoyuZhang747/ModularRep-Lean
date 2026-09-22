import ModularRep.PaperProofs.TypeBCentralKernelTripleCarriers
import ModularRep.PaperProofs.TypeBCentralKernelNormalizerInertia

/-!
# Literal quotient projections on the two bases of the inertia triple

The image subgroups in T/P and their local intersection are identified by
the actual quotient maps. The normalizer projection is the same qN used to
descend the ordinary weight. These are group-theoretic deductions; no
character equation or block-triple witness is an external premise.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelTripleProjection

open TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleCertificate
open TypeBCentralKernelNormalizerInertia TypeBCentralKernelWeightTransport

universe u

section CommonKernel

variable {X Y Z : Type u} [Group X] [Group Y] [Group Z]

def commonKernelEquiv (f : X →* Y) (hf : Function.Surjective f)
    (g : X →* Z) (hg : Function.Surjective g) (hker : f.ker = g.ker) : Y ≃* Z :=
  (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))

theorem commonKernelEquiv_apply (f : X →* Y) (hf : Function.Surjective f)
    (g : X →* Z) (hg : Function.Surjective g) (hker : f.ker = g.ker) (x : X) :
    commonKernelEquiv f hf g hg hker (f x) = g x := by
  have point : QuotientGroup.quotientKerEquivOfSurjective f hf
      (QuotientGroup.mk' f.ker x) = f x := rfl
  rw [← point]
  unfold commonKernelEquiv
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

end CommonKernel

section QuotientImages

variable {T : Type u} [Group T] (Z N H : Subgroup T) [Z.Normal]

theorem quotientSubgroupMap_surjective :
    Function.Surjective (quotientSubgroupMap Z N) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- Membership of the quotient local intersection lifts to the original
intersection because the quotient kernel is contained in N. -/
theorem quotientLocalMap_surjective (hZN : Z ≤ N) :
    Function.Surjective (quotientLocalMap Z N H) := by
  rintro ⟨⟨x, hxH⟩, hxN⟩
  obtain ⟨h, hh, rfl⟩ := hxH
  have hpre : (N.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) = N :=
    Subgroup.comap_map_eq_self (by simpa only [QuotientGroup.ker_mk'] using hZN)
  have hn : h ∈ N := by
    change h ∈ (N.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) at hxN
    rwa [hpre] at hxN
  exact ⟨⟨⟨h, hh⟩, hn⟩, rfl⟩

theorem quotientSubgroupMap_kernel_isPGroup {p : ℕ} (hZ : IsPGroup p Z) :
    IsPGroup p (quotientSubgroupMap Z N).ker := by
  have kernel : (quotientSubgroupMap Z N).ker = Z.comap N.subtype := by
    ext n
    constructor
    · intro hn
      exact (QuotientGroup.eq_one_iff (N := Z) n.val).mp (congrArg Subtype.val hn)
    · intro hn
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := Z) n.val).mpr hn
  rw [kernel]
  exact hZ.comap_subtype

theorem quotientLocalMap_kernel_isPGroup {p : ℕ} (hZ : IsPGroup p Z) :
    IsPGroup p (quotientLocalMap Z N H).ker := by
  have kernel : (quotientLocalMap Z N H).ker =
      (Z.comap H.subtype).comap (localBase N H).subtype := by
    ext x
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := Z) x.val.val).mp
        (congrArg (fun y : localBase (N.map (QuotientGroup.mk' Z))
          (H.map (QuotientGroup.mk' Z)) => y.val.val) hx)
    · intro hx
      apply Subtype.ext
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := Z) x.val.val).mpr hx
  rw [kernel]
  have hZH : IsPGroup p (Z.comap H.subtype) := hZ.comap_subtype
  exact hZH.comap_subtype

end QuotientImages

section Base

variable {A : Type u} [Group A]
  (P G T : Subgroup A) [P.Normal] (hGT : G ≤ T)

abbrev N := inside G T
abbrev Z := inside P T
abbrev Nbar := (N G T).map (QuotientGroup.mk' (Z P T))

def baseProjectionHom : G →* Nbar P G T :=
  (quotientSubgroupMap (Z P T) (N G T)).comp (insideEquiv G T hGT).toMonoidHom

theorem baseProjectionHom_surjective : Function.Surjective (baseProjectionHom P G T hGT) :=
  (quotientSubgroupMap_surjective (Z P T) (N G T)).comp (insideEquiv G T hGT).surjective

theorem baseProjectionHom_ker : (baseProjectionHom P G T hGT).ker = kernelInG G P := by
  ext g
  constructor
  · intro hg
    have value := congrArg Subtype.val hg
    change QuotientGroup.mk' (Z P T) (insideEquiv G T hGT g).val = 1 at value
    exact (QuotientGroup.eq_one_iff (N := Z P T) (insideEquiv G T hGT g).val).mp value
  · intro hg
    apply Subtype.ext
    change QuotientGroup.mk' (Z P T) (insideEquiv G T hGT g).val = 1
    exact (QuotientGroup.eq_one_iff _).mpr hg

/-- Canonical image of the base in T/P, identified with G/P by projection. -/
def baseProjectionEquiv : Nbar P G T ≃* QuotientG G P :=
  commonKernelEquiv (baseProjectionHom P G T hGT) (baseProjectionHom_surjective P G T hGT)
    (qG G P) (QuotientGroup.mk'_surjective (kernelInG G P))
    ((baseProjectionHom_ker P G T hGT).trans (QuotientGroup.ker_mk' _).symm)

theorem baseProjectionEquiv_mk (g : G) :
    baseProjectionEquiv P G T hGT
      (quotientSubgroupMap (Z P T) (N G T) (insideEquiv G T hGT g)) = qG G P g :=
  commonKernelEquiv_apply _ _ _ _ _ g

theorem baseProjection_square (x : N G T) :
    baseProjectionEquiv P G T hGT (quotientSubgroupMap (Z P T) (N G T) x) =
      qG G P ((insideEquiv G T hGT).symm x) := by
  obtain ⟨g, rfl⟩ := (insideEquiv G T hGT).surjective x
  rw [MulEquiv.symm_apply_apply]
  exact baseProjectionEquiv_mk P G T hGT g

end Base

section Local

variable {A : Type u} [Group A] [Finite A]
  {p : ℕ} {K : Type u} [Field K] [CharZero K]
  (P G T : Subgroup A) [P.Normal] [G.Normal]
  (hPG : P ≤ G) (hP : IsPGroup p (kernelInG G P))
  (W : CharacterWeight p K G) (hUT : U G W ≤ T)

abbrev H := inside (U G W) T
abbrev Hbar := (H G T W).map (QuotientGroup.mk' (Z P T))
abbrev M := localBase (N G T) (H G T W)
abbrev Mbar := localBase (Nbar P G T) (Hbar P G T W)

def normalizerTripleEquiv : Subgroup.normalizer (W.subgroup : Set G) ≃* M G T W :=
  (normalizerEquivLocalBase G W).trans (nestedLocalEquiv G T (U G W) hUT)

@[simp] theorem normalizerTripleEquiv_value (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (normalizerTripleEquiv G T W hUT x).val.val.val = ((x : G) : A) := rfl

def localProjectionHom : Subgroup.normalizer (W.subgroup : Set G) →* Mbar P G T W :=
  (quotientLocalMap (Z P T) (N G T) (H G T W)).comp
    (normalizerTripleEquiv G T W hUT).toMonoidHom

include hPG in
theorem localProjectionHom_surjective : Function.Surjective (localProjectionHom P G T W hUT) :=
  (quotientLocalMap_surjective (Z P T) (N G T) (H G T W)
    (Subgroup.comap_mono hPG)).comp (normalizerTripleEquiv G T W hUT).surjective

/-- This is the already checked ordinary weight descent on its literal carrier. -/
def quotientWeight : CharacterWeight p K (QuotientG G P) :=
  descend (qG G P) (qG_surjective G P) (quotientKernelIsPGroup G P hP) W

def normalizerProjectionHom : Subgroup.normalizer (W.subgroup : Set G) →*
    Subgroup.normalizer ((quotientWeight P G hP W).subgroup : Set (QuotientG G P)) :=
  normalizerMap (qG G P) W.subgroup

theorem normalizerProjectionHom_surjective :
    Function.Surjective (normalizerProjectionHom P G hP W) :=
  normalizerMap_surjective (qG G P) (qG_surjective G P) W.subgroup
    (TypeBCentralKernelWeightTransport.kernel_le_radical (qG G P)
      (quotientKernelIsPGroup G P hP) W)

theorem localProjectionHom_ker :
    (localProjectionHom P G T W hUT).ker = (normalizerProjectionHom P G hP W).ker := by
  ext x
  constructor
  · intro hx
    have value := congrArg (fun y : Mbar P G T W => y.val.val) hx
    change QuotientGroup.mk' (Z P T) (normalizerTripleEquiv G T W hUT x).val.val = 1 at value
    have hp : ((x : G) : A) ∈ P :=
      (QuotientGroup.eq_one_iff (N := Z P T) (normalizerTripleEquiv G T W hUT x).val.val).mp value
    apply Subtype.ext
    change qG G P (x : G) = 1
    exact (QuotientGroup.eq_one_iff _).mpr hp
  · intro hx
    have value := congrArg Subtype.val hx
    change qG G P (x : G) = 1 at value
    have hp : ((x : G) : A) ∈ P :=
      (QuotientGroup.eq_one_iff (N := kernelInG G P) (x : G)).mp value
    apply Subtype.ext
    apply Subtype.ext
    change QuotientGroup.mk' (Z P T) (normalizerTripleEquiv G T W hUT x).val.val = 1
    exact (QuotientGroup.eq_one_iff _).mpr hp

/-- The canonical local image intersection in T/P is the actual normalizer
of the descended radical, with the prescribed qN map on every element. -/
def normalizerProjectionEquiv : Mbar P G T W ≃*
    Subgroup.normalizer ((quotientWeight P G hP W).subgroup : Set (QuotientG G P)) :=
  commonKernelEquiv (localProjectionHom P G T W hUT)
    (localProjectionHom_surjective P G T hPG W hUT)
    (normalizerProjectionHom P G hP W) (normalizerProjectionHom_surjective P G hP W)
    (localProjectionHom_ker P G T hP W hUT)

theorem normalizerProjectionEquiv_mk (x : Subgroup.normalizer (W.subgroup : Set G)) :
    normalizerProjectionEquiv P G T hPG hP W hUT
      (quotientLocalMap (Z P T) (N G T) (H G T W) (normalizerTripleEquiv G T W hUT x)) =
      normalizerProjectionHom P G hP W x :=
  commonKernelEquiv_apply _ _ _ _ _ x

theorem normalizerProjection_square (x : M G T W) :
    normalizerProjectionEquiv P G T hPG hP W hUT
      (quotientLocalMap (Z P T) (N G T) (H G T W) x) =
      normalizerProjectionHom P G hP W ((normalizerTripleEquiv G T W hUT).symm x) := by
  obtain ⟨x, rfl⟩ := (normalizerTripleEquiv G T W hUT).surjective x
  rw [MulEquiv.symm_apply_apply]
  exact normalizerProjectionEquiv_mk P G T hPG hP W hUT x

end Local

end ModularRep.PaperProofs.TypeBCentralKernelTripleProjection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
