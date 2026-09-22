import ModularRep.PaperProofs.TypeBCentralKernelCarriers
import ModularRep.PaperProofs.TypeBAutomorphismSource
import ModularRep.PaperProofs.TypeBSpinCoverSource

/-!
# The central two-kernel on the literal Spin and ambient carriers

The kernel is the image of `Z(Spin)` in `D0 semidirect FieldGroup`, not the
image of `Z(D0)`. Its ambient normality follows from the checked actual
conjugation action. Quotient identifications and their generator values are
constructed; `Omega` is the existing literal quotient `Spin / Z(Spin)`.

The only new numerical source is the order of the finite Spin centre, with
the original odd-field and rank guards. Malle--Testerman Proposition 9.15
and Table 9.2, pp. 71--72, and Corollary 24.13, p. 211, identify the
geometric type B point-centre. The additional identification of the centre
of the literal finite Clifford norm kernel with those central fixed points
is an explicit E1/U source-model join. Tables 24.2--24.3 and Remark 24.19,
pp. 211--214, give the existing named-cover context; they are not substituted
for that finite-centre identification. The order-two source includes (3,3).
No equality with the two-core, cover maximality, or representation theoretic
target is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCentralKernelSpinBinding

open ModularRep TypeBCliffordCarriers TypeBWeightStabilizerSource
open TypeBAutomorphismSource TypeBCentralKernelCarriers

variable {n p f : ℕ} {F : Type}
variable [Field F] [Finite F] [CharP F p]
variable {N : NormSource n F} {parameters : OddFieldParameters F p f}
variable (S : FieldActionSource n F p f parameters N)

abbrev A := Ambient S
abbrev G : Subgroup (A S) := embeddedSpin S

/-- The actual central kernel, distinguished from the special Clifford centre. -/
def P : Subgroup (A S) :=
  (Subgroup.center (Spin n F N)).map (spinEmbedding S)

/-- Canonical identification of Spin with its actual ambient image. -/
def spinEquiv : Spin n F N ≃* G S :=
  MonoidHom.ofInjective (spinEmbedding_injective S)

@[simp] theorem spinEquiv_val (x : Spin n F N) :
    (spinEquiv S x : A S) = spinEmbedding S x := rfl

instance G_normal : (G S).Normal where
  conj_mem _ hx a := by
    obtain ⟨x, rfl⟩ := hx
    exact ⟨ambientAutomorphism S a x, spinEmbedding_natural S a x⟩

theorem P_le_G : P S ≤ G S := by
  rintro a ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- Every actual ambient automorphism preserves the Spin centre. -/
theorem ambient_preserves_spin_center (a : A S) (x : Spin n F N)
    (hx : x ∈ Subgroup.center (Spin n F N)) :
    ambientAutomorphism S a x ∈ Subgroup.center (Spin n F N) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := (ambientAutomorphism S a).surjective y
  simpa only [map_mul] using
    congrArg (ambientAutomorphism S a) (Subgroup.mem_center_iff.mp hx y)

instance P_normal : (P S).Normal where
  conj_mem _ hx a := by
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨ambientAutomorphism S a x, ambient_preserves_spin_center S a x hx,
      spinEmbedding_natural S a x⟩

def centreEquiv : Subgroup.center (Spin n F N) ≃* P S :=
  (Subgroup.center (Spin n F N)).equivMapOfInjective
    (spinEmbedding S) (spinEmbedding_injective S)

@[simp] theorem centreEquiv_val (x : Subgroup.center (Spin n F N)) :
    (centreEquiv S x : A S) = spinEmbedding S x := rfl

@[simp] theorem kernel_mem_spinEquiv (x : Spin n F N) :
    spinEquiv S x ∈ kernelInG (G S) (P S) ↔
      x ∈ Subgroup.center (Spin n F N) := by
  change spinEmbedding S x ∈ P S ↔ _
  constructor
  · rintro ⟨z, hz, heq⟩
    exact (spinEmbedding_injective S heq) ▸ hz
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem spinEquiv_center_iff (x : Spin n F N) :
    spinEquiv S x ∈ Subgroup.center (G S) ↔
      x ∈ Subgroup.center (Spin n F N) := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply (spinEquiv S).injective
    simpa only [map_mul] using h (spinEquiv S y)
  · intro h y
    obtain ⟨y, rfl⟩ := (spinEquiv S).surjective y
    simpa only [map_mul] using congrArg (spinEquiv S) (h y)

/-- The kernel inside the embedded base is exactly that base's centre. -/
theorem kernel_eq_center : kernelInG (G S) (P S) = Subgroup.center (G S) := by
  ext x
  obtain ⟨x, rfl⟩ := (spinEquiv S).surjective x
  exact (kernel_mem_spinEquiv S x).trans (spinEquiv_center_iff S x).symm

theorem kernel_central : kernelInG (G S) (P S) ≤ Subgroup.center (G S) :=
  (kernel_eq_center S).le

theorem centre_map_kernel :
    (Subgroup.center (Spin n F N)).map (spinEquiv S).toMonoidHom =
      kernelInG (G S) (P S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (kernel_mem_spinEquiv S x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := (spinEquiv S).surjective y
    exact ⟨x, (kernel_mem_spinEquiv S x).mp hy, rfl⟩

/-- The finite-centre equation is the sole new source field. Its scope
contains the exceptional field/rank pair as well as the generic pairs. -/
structure SpinCentreOrderSource (n p f : ℕ) (F : Type)
    [Field F] [Finite F] [CharP F p] (N : NormSource n F) where
  centre_order : OddFieldParameters F p f → 3 ≤ n →
    Nat.card (Subgroup.center (Spin n F N)) = 2

theorem P_card (source : SpinCentreOrderSource n p f F N) (rank : 3 ≤ n) :
    Nat.card (P S) = 2 := by
  rw [← Nat.card_congr (centreEquiv S).toEquiv]
  exact source.centre_order parameters rank

theorem P_isTwoGroup (source : SpinCentreOrderSource n p f F N) (rank : 3 ≤ n) :
    IsPGroup 2 (P S) := by
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using P_card S source rank

theorem kernel_isTwoGroup
    (source : SpinCentreOrderSource n p f F N) (rank : 3 ≤ n) :
    IsPGroup 2 (kernelInG (G S) (P S)) :=
  (P_isTwoGroup S source rank).comap_subtype

/-- The literal Omega quotient mapped to the quotient of the embedded Spin. -/
def omegaQuotientEquiv : TypeBSpinCoverSource.Omega N ≃*
    QuotientG (G S) (P S) :=
  QuotientGroup.congr (Subgroup.center (Spin n F N))
    (kernelInG (G S) (P S)) (spinEquiv S) (centre_map_kernel S)

@[simp] theorem omegaQuotientEquiv_mk (x : Spin n F N) :
    omegaQuotientEquiv S (QuotientGroup.mk' (Subgroup.center (Spin n F N)) x) =
      qG (G S) (P S) (spinEquiv S x) := rfl

def spinOmegaEquiv : QuotientG (G S) (P S) ≃* TypeBSpinCoverSource.Omega N :=
  (omegaQuotientEquiv S).symm

@[simp] theorem spinOmegaEquiv_mk (x : Spin n F N) :
    spinOmegaEquiv S (qG (G S) (P S) (spinEquiv S x)) =
      QuotientGroup.mk' (Subgroup.center (Spin n F N)) x := by
  change (omegaQuotientEquiv S).symm (qG (G S) (P S) (spinEquiv S x)) = _
  rw [← omegaQuotientEquiv_mk]
  exact (omegaQuotientEquiv S).symm_apply_apply _

/-- This inclusion binds Omega to the actual image of Spin in A/P. -/
def omegaEmbedding : TypeBSpinCoverSource.Omega N →* QuotientA (P S) :=
  (quotientEmbedding (G S) (P S)).comp (omegaQuotientEquiv S).toMonoidHom

@[simp] theorem omegaEmbedding_mk (x : Spin n F N) :
    omegaEmbedding S (QuotientGroup.mk' (Subgroup.center (Spin n F N)) x) =
      qA (P S) (spinEmbedding S x) := rfl

theorem omegaEmbedding_injective : Function.Injective (omegaEmbedding S) :=
  (quotientEmbedding_injective (G S) (P S)).comp (omegaQuotientEquiv S).injective

def omegaEmbeddedEquiv : TypeBSpinCoverSource.Omega N ≃*
    embeddedQuotientG (G S) (P S) :=
  (omegaQuotientEquiv S).trans (quotientEquiv (G S) (P S))

@[simp] theorem omegaEmbeddedEquiv_val (x : TypeBSpinCoverSource.Omega N) :
    (omegaEmbeddedEquiv S x : QuotientA (P S)) = omegaEmbedding S x := rfl

theorem spinEquiv_action (a : A S) (x : Spin n F N) :
    spinEquiv S (ambientAutomorphism S a x) =
      originalAction (G S) a (spinEquiv S x) := by
  apply Subtype.ext
  exact spinEmbedding_natural S a x

/-- The Omega action is the actual quotient conjugation transported through
the constructed quotient equivalence. -/
def omegaAction : QuotientA (P S) →* MulAut (TypeBSpinCoverSource.Omega N) :=
  (MulAut.congr (omegaQuotientEquiv S)).symm.toMonoidHom.comp
    (quotientAction (G S) (P S))

theorem omegaAction_equiv (a : QuotientA (P S)) (x : TypeBSpinCoverSource.Omega N) :
    omegaQuotientEquiv S (omegaAction S a x) =
      quotientAction (G S) (P S) a (omegaQuotientEquiv S x) := by
  change omegaQuotientEquiv S ((omegaQuotientEquiv S).symm _) = _
  exact (omegaQuotientEquiv S).apply_symm_apply _

theorem omegaAction_embedding (a : QuotientA (P S)) (x : TypeBSpinCoverSource.Omega N) :
    omegaEmbedding S (omegaAction S a x) = a * omegaEmbedding S x * a⁻¹ := by
  change quotientEmbedding (G S) (P S) (omegaQuotientEquiv S (omegaAction S a x)) = _
  rw [omegaAction_equiv, quotientAction_embedding]
  rfl

/-- Generator formula retaining the same actual ambient element and Spin point. -/
theorem omegaAction_mk (a : A S) (x : Spin n F N) :
    omegaAction S (qA (P S) a)
        (QuotientGroup.mk' (Subgroup.center (Spin n F N)) x) =
      QuotientGroup.mk' (Subgroup.center (Spin n F N)) (ambientAutomorphism S a x) := by
  apply (omegaQuotientEquiv S).injective
  rw [omegaAction_equiv, omegaQuotientEquiv_mk, omegaQuotientEquiv_mk,
    quotientAction_mk, spinEquiv_action]

end ModularRep.PaperProofs.TypeBCentralKernelSpinBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
