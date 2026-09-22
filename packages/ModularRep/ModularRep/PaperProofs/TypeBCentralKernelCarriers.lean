import ModularRep.NormalCoreTransport
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual group and actor carriers for a central ell-kernel

The ambient and base groups are the literal normal subgroups `P ≤ G ≤ A`.
The quotient base is `G / (P.subgroupOf G)` and its embedding into `A/P`
is constructed from the original inclusion. All quotient actions are actual
conjugation actions through this embedding. Centrality in `G` also makes
the original action on `G` factor through `A/P`.

The final group-only helpers specialize the checked radical and normalizer
quotient transport to this same kernel. The ell-core is used only to prove
that an arbitrary normal ell-subgroup lies in every radical subgroup. No
equality with the ell-core, no Spin centre identification, no block source,
and no character, weight or inductive-condition conclusion is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCentralKernelCarriers

universe u

variable {A : Type u} [Group A]
variable (G P : Subgroup A) [G.Normal] [P.Normal]

/-- The specified kernel as an actual subgroup of the base group. -/
abbrev kernelInG : Subgroup G := P.subgroupOf G

abbrev QuotientG := G ⧸ kernelInG G P
abbrev QuotientA := A ⧸ P

def qG : G →* QuotientG G P := QuotientGroup.mk' (kernelInG G P)
def qA : A →* QuotientA P := QuotientGroup.mk' P

theorem qG_surjective : Function.Surjective (qG G P) :=
  QuotientGroup.mk'_surjective _

theorem qA_surjective : Function.Surjective (qA P) :=
  QuotientGroup.mk'_surjective _

@[simp] theorem qG_ker : (qG G P).ker = kernelInG G P := QuotientGroup.ker_mk' _
@[simp] theorem qA_ker : (qA P).ker = P := QuotientGroup.ker_mk' _

/-- The image of the actual normal base subgroup in the ambient quotient. -/
abbrev embeddedQuotientG : Subgroup (QuotientA P) := G.map (qA P)

instance embeddedQuotientG_normal : (embeddedQuotientG G P).Normal :=
  (inferInstance : G.Normal).map (qA P) (qA_surjective P)

/-- The quotient of the original subgroup inclusion. -/
def quotientEmbedding : QuotientG G P →* QuotientA P :=
  QuotientGroup.map (kernelInG G P) P G.subtype
    (show kernelInG G P ≤ P.comap G.subtype from le_rfl)

@[simp] theorem quotientEmbedding_mk (g : G) :
    quotientEmbedding G P (qG G P g) = qA P (g : A) := rfl

theorem quotientEmbedding_injective : Function.Injective (quotientEmbedding G P) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact (QuotientGroup.ker_map (kernelInG G P) P G.subtype
    (show kernelInG G P ≤ P.comap G.subtype from le_rfl)).trans
      (QuotientGroup.map_mk'_self (kernelInG G P))

theorem quotientEmbedding_range :
    (quotientEmbedding G P).range = embeddedQuotientG G P := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := qG_surjective G P x
    exact ⟨g.1, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨qG G P ⟨g, hg⟩, rfl⟩

/-- The first-isomorphism identification uses the same quotient inclusion
on every point, not an unrelated isomorphism of the two finite groups. -/
def quotientEquiv : QuotientG G P ≃* embeddedQuotientG G P :=
  (MonoidHom.ofInjective (quotientEmbedding_injective G P)).trans
    (MulEquiv.subgroupCongr (quotientEmbedding_range G P))

@[simp] theorem quotientEquiv_val (x : QuotientG G P) :
    (quotientEquiv G P x : QuotientA P) = quotientEmbedding G P x := rfl

@[simp] theorem quotientEquiv_mk_val (g : G) :
    (quotientEquiv G P (qG G P g) : QuotientA P) = qA P (g : A) := rfl

/-- The original ambient action is literally conjugation on the normal subgroup. -/
def originalAction : A →* MulAut G := MulAut.conjNormal (H := G)

@[simp] theorem originalAction_val (a : A) (g : G) :
    (originalAction G a g : A) = a * (g : A) * a⁻¹ := rfl

/-- The specified kernel is preserved by each actual ambient conjugation. -/
theorem kernelInG_map_originalAction (a : A) :
    (kernelInG G P).map (originalAction G a).toMonoidHom = kernelInG G P := by
  have stable : ∀ (b : A) (x : G), x ∈ kernelInG G P →
      originalAction G b x ∈ kernelInG G P := by
    intro b x hx
    exact (inferInstance : P.Normal).conj_mem x.1 hx b
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact stable a y hy
  · intro hx
    refine ⟨originalAction G a⁻¹ x, stable a⁻¹ x hx, ?_⟩
    change originalAction G a (originalAction G a⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

/-- Actual conjugation in `A/P`, transported to the literal quotient `G/P`. -/
def quotientAction : QuotientA P →* MulAut (QuotientG G P) :=
  (MulAut.congr (quotientEquiv G P)).symm.toMonoidHom.comp
    (MulAut.conjNormal (H := embeddedQuotientG G P))

theorem quotientAction_equiv (a : QuotientA P) (x : QuotientG G P) :
    quotientEquiv G P (quotientAction G P a x) =
      MulAut.conjNormal (H := embeddedQuotientG G P) a (quotientEquiv G P x) := by
  change quotientEquiv G P ((quotientEquiv G P).symm
    (MulAut.conjNormal (H := embeddedQuotientG G P) a (quotientEquiv G P x))) = _
  exact (quotientEquiv G P).apply_symm_apply _

/-- The quotient actor has the exact original conjugation value in `A/P`. -/
theorem quotientAction_embedding (a : QuotientA P) (x : QuotientG G P) :
    quotientEmbedding G P (quotientAction G P a x) =
      a * quotientEmbedding G P x * a⁻¹ := by
  change (quotientEquiv G P (quotientAction G P a x) : QuotientA P) = _
  rw [quotientAction_equiv]
  rfl

/-- The original and quotient actions commute with the actual projection. -/
theorem quotientAction_mk (a : A) (g : G) :
    quotientAction G P (qA P a) (qG G P g) =
      qG G P (originalAction G a g) := by
  apply quotientEmbedding_injective G P
  rw [quotientAction_embedding, quotientEmbedding_mk, quotientEmbedding_mk]
  change qA P a * qA P (g : A) * (qA P a)⁻¹ =
    qA P (a * (g : A) * a⁻¹)
  simp only [map_mul, map_inv]

/-- Homomorphism form of the same group/action square. -/
theorem quotientAction_square (a : A) :
    (qG G P).comp (originalAction G a).toMonoidHom =
      (quotientAction G P (qA P a)).toMonoidHom.comp (qG G P) := by
  apply MonoidHom.ext
  intro g
  exact (quotientAction_mk G P a g).symm

section Centrality

variable (hPG : P ≤ G) (central : kernelInG G P ≤ Subgroup.center G)

include hPG central

/-- Centrality is imposed on the actual kernel inside `G`; every such
ambient kernel element acts trivially on the original base group. -/
theorem kernel_fixes_original (p : P) (g : G) :
    originalAction G (p : A) g = g := by
  have hc := Subgroup.mem_center_iff.mp
    (central (show (⟨p.1, hPG p.2⟩ : G) ∈ kernelInG G P from p.2)) g
  have hcA : (g : A) * (p : A) = (p : A) * (g : A) :=
    congrArg (fun x : G => (x : A)) hc
  apply Subtype.ext
  change (p : A) * (g : A) * (p : A)⁻¹ = (g : A)
  rw [← hcA]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem kernel_le_originalAction_ker : P ≤ (originalAction G).ker := by
  intro p hp
  apply MulEquiv.ext
  intro g
  exact kernel_fixes_original G P hPG central ⟨p, hp⟩ g

/-- Since the kernel is central in `G`, even the original action on `G`
factors through the actual ambient quotient. -/
def originalQuotientAction : QuotientA P →* MulAut G :=
  QuotientGroup.lift P (originalAction G)
    (kernel_le_originalAction_ker G P hPG central)

@[simp] theorem originalQuotientAction_mk (a : A) :
    originalQuotientAction G P hPG central (qA P a) = originalAction G a := rfl

theorem originalQuotientAction_square (a : QuotientA P) (g : G) :
    qG G P (originalQuotientAction G P hPG central a g) =
      quotientAction G P a (qG G P g) := by
  obtain ⟨a, rfl⟩ := qA_surjective P a
  exact (quotientAction_mk G P a g).symm

end Centrality

section RadicalAndLocalQuotients

variable [Finite A] {ell : ℕ} (hEll : Nat.Prime ell) (hP : IsPGroup ell P)

include hP

theorem kernelInG_isPGroup : IsPGroup ell (kernelInG G P) := hP.comap_subtype

include hEll

/-- The kernel is contained in every radical subgroup, without asserting
that the kernel is itself the full ell-core. -/
theorem kernel_le_radical (Q : Subgroup G) (hQ : IsRadicalSubgroup ell Q) :
    kernelInG G P ≤ Q :=
  (normal_pSubgroup_le_pCore ell (kernelInG G P) (kernelInG_isPGroup G P hP)).trans
    (pCore_le_of_isRadicalSubgroup hEll Q hQ)

omit hEll hP in
def radicalImage (Q : Subgroup G) : Subgroup (QuotientG G P) := Q.map (qG G P)
omit hEll hP in
def radicalPreimage (Q : Subgroup (QuotientG G P)) : Subgroup G := Q.comap (qG G P)

theorem radicalImage_radical (Q : Subgroup G) (hQ : IsRadicalSubgroup ell Q) :
    IsRadicalSubgroup ell (radicalImage G P Q) := by
  apply (isRadicalSubgroup_iff_map_surjective_of_ker_le
    (qG G P) (qG_surjective G P) Q ?_ ?_).mp hQ
  · rw [qG_ker]
    exact kernel_le_radical G P hEll hP Q hQ
  · rw [qG_ker]
    exact kernelInG_isPGroup G P hP

theorem radicalPreimage_image (Q : Subgroup G) (hQ : IsRadicalSubgroup ell Q) :
    radicalPreimage G P (radicalImage G P Q) = Q := by
  apply Subgroup.comap_map_eq_self
  rw [qG_ker]
  exact kernel_le_radical G P hEll hP Q hQ

omit hEll hP in
theorem radicalImage_preimage (Q : Subgroup (QuotientG G P)) :
    radicalImage G P (radicalPreimage G P Q) = Q := by
  apply Subgroup.map_comap_eq_self
  intro x _
  exact qG_surjective G P x

omit hEll in
theorem radicalPreimage_radical (Q : Subgroup (QuotientG G P))
    (hQ : IsRadicalSubgroup ell Q) :
    IsRadicalSubgroup ell (radicalPreimage G P Q) := by
  apply (isRadicalSubgroup_iff_map_surjective_of_ker_le
    (qG G P) (qG_surjective G P) (radicalPreimage G P Q)
    (Subgroup.ker_le_comap _ _) ?_).mpr
  · change IsRadicalSubgroup ell (radicalImage G P (radicalPreimage G P Q))
    rw [radicalImage_preimage]
    exact hQ
  · rw [qG_ker]
    exact kernelInG_isPGroup G P hP

/-- Actual radical subgroup carriers are in bijection by image/preimage. -/
def radicalEquiv : {Q : Subgroup G // IsRadicalSubgroup ell Q} ≃
    {Q : Subgroup (QuotientG G P) // IsRadicalSubgroup ell Q} where
  toFun Q := ⟨radicalImage G P Q.1, radicalImage_radical G P hEll hP Q.1 Q.2⟩
  invFun Q := ⟨radicalPreimage G P Q.1, radicalPreimage_radical G P hP Q.1 Q.2⟩
  left_inv Q := Subtype.ext (radicalPreimage_image G P hEll hP Q.1 Q.2)
  right_inv Q := Subtype.ext (radicalImage_preimage G P Q.1)

/-- The same radical image gives the canonical local normalizer quotient
equivalence used by the later weight and triple transports. -/
def localQuotientEquiv (Q : Subgroup G) (hQ : IsRadicalSubgroup ell Q) :
    NormalizerQuotient Q ≃* NormalizerQuotient (radicalImage G P Q) :=
  normalizerQuotientEquivOfSurjectiveOfKerLE (qG G P) (qG_surjective G P) Q (by
    rw [qG_ker]
    exact kernel_le_radical G P hEll hP Q hQ)

theorem normalizer_image (Q : Subgroup G) (hQ : IsRadicalSubgroup ell Q) :
    (Subgroup.normalizer (Q : Set G)).map (qG G P) =
      Subgroup.normalizer ((radicalImage G P Q : Subgroup (QuotientG G P)) : Set _) :=
  map_normalizer_eq_of_surjective_of_ker_le (qG G P) (qG_surjective G P) Q (by
    rw [qG_ker]
    exact kernel_le_radical G P hEll hP Q hQ)

end RadicalAndLocalQuotients

end ModularRep.PaperProofs.TypeBCentralKernelCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
