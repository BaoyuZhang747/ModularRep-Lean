import ModularRep.PaperProofs.TypeBBSCentralQuotientPairTransport

/-!
# Conjugation images of the selected character quotient

Conjugation on the actual projected base is expressed on the original
normal subgroup. Full original action image gives the complete character
stabilizer. The same raw inertia inclusion gives the complete local image.
These group deductions retain the original character and raw weight.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQuotientInertiaConjugationImage

open ModularRep
open TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelTripleCertificate TypeBCentralKernelButterflyCertificate
open TypeBBSCentralQuotientPairTransport

variable {p : ℕ} {k K A : Type}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A]
  (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)
  (centreless : Subgroup.center G = ⊥)

/-- The projected base is identified by the actual inclusion and projection. -/
def sourceBaseEquiv : G ≃* quotientBase G root theta centreless :=
  (TypeBCentralKernelTripleCharacters.baseEquiv G root theta).trans
    (TypeBBSCentralQuotientPairTransport.baseEquiv G root theta centreless)

/-- Conjugation on that base, expressed on the original group. -/
def sourceAction :
    (T G root theta ⧸ ambientKernel G root theta centreless) →* MulAut G :=
  (MulAut.congr (sourceBaseEquiv G root theta centreless)).symm.toMonoidHom.comp
    (firstAction (quotientBase G root theta centreless))

theorem sourceAction_projection (t : T G root theta) :
    sourceAction G root theta centreless (ambientEquiv G root theta centreless t) =
      originalAction G (t : A) := by
  apply MulEquiv.ext
  intro x
  apply (sourceBaseEquiv G root theta centreless).injective
  change (sourceBaseEquiv G root theta centreless)
    ((sourceBaseEquiv G root theta centreless).symm
      (firstAction (quotientBase G root theta centreless)
        (ambientEquiv G root theta centreless t)
        (sourceBaseEquiv G root theta centreless x))) =
    sourceBaseEquiv G root theta centreless (originalAction G (t : A) x)
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  change (QuotientGroup.mk' (ambientKernel G root theta centreless)) t *
      (QuotientGroup.mk' (ambientKernel G root theta centreless))
        (baseInclusion G root theta x) *
      ((QuotientGroup.mk' (ambientKernel G root theta centreless)) t)⁻¹ =
    (QuotientGroup.mk' (ambientKernel G root theta centreless))
      (baseInclusion G root theta (originalAction G (t : A) x))
  rw [← map_mul, ← map_inv, ← map_mul]
  apply congrArg (QuotientGroup.mk' (ambientKernel G root theta centreless))
  apply Subtype.ext
  rfl

/-- The projected character inertia has the whole character stabilizer as image. -/
theorem sourceAction_range
    (full : Function.Surjective (originalAction G)) :
    (sourceAction G root theta centreless).range =
      brauerStabilizer (MonoidHom.id (MulAut G)) root theta := by
  ext alpha
  constructor
  · rintro ⟨tbar, rfl⟩
    obtain ⟨t, rfl⟩ := (ambientEquiv G root theta centreless).surjective tbar
    rw [sourceAction_projection]
    rw [mem_brauerStabilizer]
    have ht := (mem_brauerStabilizer (originalAction G) root theta (t : A)).mp
      t.property
    simpa only [MonoidHom.id_apply, map_inv] using ht
  · intro ha
    obtain ⟨a, rfl⟩ := full alpha
    have ht : a ∈ T G root theta := by
      rw [mem_brauerStabilizer] at ha ⊢
      simpa only [MonoidHom.id_apply, map_inv] using ha
    exact ⟨ambientEquiv G root theta centreless ⟨a, ht⟩,
      sourceAction_projection G root theta centreless ⟨a, ht⟩⟩

/-- The local image is the full raw-weight stabilizer, using the same U ≤ T. -/
theorem sourceLocalAction_image
    (full : Function.Surjective (originalAction G))
    (W : CharacterWeight p K G) (hUT : U G W ≤ T G root theta) :
    (quotientLocalAmbient G root theta centreless W).map
        (sourceAction G root theta centreless) =
      rawStabilizer (MonoidHom.id (MulAut G)) W := by
  ext alpha
  constructor
  · rintro ⟨tbar, htbar, rfl⟩
    obtain ⟨t, ht, rfl⟩ := htbar
    change sourceAction G root theta centreless
      (ambientEquiv G root theta centreless t) ∈
        rawStabilizer (MonoidHom.id (MulAut G)) W
    rw [sourceAction_projection, mem_rawStabilizer]
    have hu := (mem_rawStabilizer (originalAction G) W (t : A)).mp ht
    simpa only [MonoidHom.id_apply, map_inv] using hu
  · intro ha
    obtain ⟨a, rfl⟩ := full alpha
    have hu : a ∈ U G W := by
      rw [mem_rawStabilizer] at ha ⊢
      simpa only [MonoidHom.id_apply, map_inv] using ha
    let t : T G root theta := ⟨a, hUT hu⟩
    refine ⟨ambientEquiv G root theta centreless t, ?_,
      sourceAction_projection G root theta centreless t⟩
    exact ⟨t, hu, rfl⟩

end ModularRep.PaperProofs.TypeBQuotientInertiaConjugationImage



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
