import ModularRep.PaperProofs.TypeBLocalOrdinaryGeometrySplitting
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Ordinary cyclic extensions on the actual split local quotient

Isaacs Corollary 11.22, p. 186, supplies the cyclic-quotient extension
theorem. Serre Sections 12.1 and 12.3, especially Theorem 24 on p. 94,
give its characteristic-zero interpretation over a field containing the
roots of unity of the fixed finite ambient group. The source below retains
that ambient group and its sufficient-root condition explicitly.

The local application uses the actual factor inertia modulo the embedded
radical. The existing normalizer geometry constructs its normal base,
local character and invariance. The resulting character fills the literal
ordinary-extension record; it is not an extension to a larger normalizer.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBLocalOrdinaryExtensionSplitting

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry
open ModularRep.ManuscriptVerification.CyclicOuterBAW

/-- The fixed-group, sufficient-splitting form of the ordinary cyclic
extension theorem. Its only field is the general character-level theorem. -/
structure ScopedCyclicExtensionSource (K H : Type)
    [Field K] [Group H] [finiteAmbient : Finite H]
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card H)] : Prop where
  extension : ∀ (B : Subgroup H) [normalB : B.Normal] (theta : Irr K B),
    IsCyclic (H ⧸ B) →
    (∀ (h : H) (x : B), theta (MulAut.conjNormal h x) = theta x) →
    ∃ thetaHat : Irr K H, ∀ x : B, thetaHat x.1 = theta x

/-- Removing the radical preserves the computed cyclic quotient and
applies the source only to the exact remaining ambient group. -/
theorem extension_over_quotient_tower
    {D C K : Type} [Group D] [Finite D] [Group C] [IsCyclic C]
    [Field K] [CharZero K]
    (Q B : Subgroup D) [Q.Normal] [B.Normal] (hQB : Q ≤ B)
    [HasEnoughRootsOfUnity K (Nat.card (D ⧸ Q))]
    (source : ScopedCyclicExtensionSource K (D ⧸ Q))
    (embedding : (D ⧸ B) →* C) (injective : Function.Injective embedding)
    (theta : Irr K (B.map (QuotientGroup.mk' Q)))
    (fixed : ∀ (d : D ⧸ Q) (x : B.map (QuotientGroup.mk' Q)),
      theta (MulAut.conjNormal d x) = theta x) :
    ∃ thetaHat : Irr K (D ⧸ Q),
      ∀ x : B.map (QuotientGroup.mk' Q), thetaHat x.1 = theta x :=
  source.extension (B.map (QuotientGroup.mk' Q)) theta
    (isCyclic_quotient_tower_of_embedding Q B hQB embedding injective) fixed

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field) (W : CharacterWeight ell K G)
variable (factor : Subgroup (Ambient field))
variable (base_le_factor : embeddedG G field ≤ factor)

/-- The order bound is on the literal inertia quotient, by two applications
of Lagrange's theorem. -/
theorem local_order_dvd_ambient :
    Nat.card (Inertia G field action W factor ⧸
      RadicalInInertia G field action W factor) ∣ Nat.card (Ambient field) :=
  (Subgroup.card_quotient_dvd_card (RadicalInInertia G field action W factor)).trans
    (Subgroup.card_subgroup_dvd_card (Inertia G field action W factor))

/-- One sufficient-root convention for the ambient group supplies the
exact sufficient-root guard of this local extension. -/
def localRoots_of_ambientRoots
    [HasEnoughRootsOfUnity K (Nat.card (Ambient field))] :
    HasEnoughRootsOfUnity K (Nat.card (Inertia G field action W factor ⧸
      RadicalInInertia G field action W factor)) :=
  HasEnoughRootsOfUnity.of_dvd K (local_order_dvd_ambient G field action W factor)

include base_le_factor in
/-- Actual local invariance and the quotient embedding supply all inputs
to the scoped theorem except its fixed-group E1 certificate. -/
theorem localOrdinaryExtension_of_cyclic_embedding
    {C : Type} [Group C] [IsCyclic C]
    [HasEnoughRootsOfUnity K (Nat.card (Inertia G field action W factor ⧸
      RadicalInInertia G field action W factor))]
    (source : ScopedCyclicExtensionSource K
      (Inertia G field action W factor ⧸ RadicalInInertia G field action W factor))
    (embedding : (Inertia G field action W factor ⧸
      BaseInInertia G field action W factor) →* C)
    (injective : Function.Injective embedding) :
    Nonempty (LocalOrdinaryExtension G field W (Inertia G field action W factor)) := by
  obtain ⟨thetaHat, hthetaHat⟩ := extension_over_quotient_tower
    (RadicalInInertia G field action W factor)
    (BaseInInertia G field action W factor)
    (by
      intro x hx
      obtain ⟨r, _hr, hrx⟩ := hx
      exact ⟨r, hrx⟩) source embedding injective
    (TypeBLocalOrdinaryGeometrySplitting.localCharacter G field action W factor base_le_factor)
    (TypeBLocalOrdinaryGeometrySplitting.localCharacter_fixed G field action W factor base_le_factor)
  refine ⟨{
    radical_le := TypeBLocalOrdinaryGeometrySplitting.radical_le_inertia
      G field action W factor base_le_factor
    radical_normal := radicalInInertia_normal G field action W factor
    normalizerInclusion := TypeBLocalOrdinaryGeometrySplitting.normalizerInclusion
      G field action W factor base_le_factor
    normalizerInclusion_value := TypeBLocalOrdinaryGeometrySplitting.normalizerInclusion_value
      G field action W factor base_le_factor
    character := thetaHat
    restriction := ?_ }⟩
  intro x
  exact (hthetaHat (TypeBLocalOrdinaryGeometrySplitting.normalizerToLocal
    G field action W factor base_le_factor x)).trans
    (TypeBLocalOrdinaryGeometrySplitting.localCharacter_on_normalizer
      G field action W factor base_le_factor x)

/-- The first ordinary extension uses the actual quotient of the
special-Clifford-side inertia and the existing embedding into M/G. -/
theorem ordinary_M
    [HasEnoughRootsOfUnity K (Nat.card (Inertia G field action W (embeddedM field) ⧸
      RadicalInInertia G field action W (embeddedM field)))]
    (source : ScopedCyclicExtensionSource K
      (Inertia G field action W (embeddedM field) ⧸
        RadicalInInertia G field action W (embeddedM field)))
    (quotient_cyclic : IsCyclic (M ⧸ G)) :
    Nonempty (LocalOrdinaryExtension G field W
      (rawNormalizerInertia G field action W ⊓ embeddedM field)) := by
  letI := embeddedG_normal G field action
  letI := quotient_cyclic
  exact localOrdinaryExtension_of_cyclic_embedding G field action W
    (embeddedM field) (embeddedG_le_embeddedM G field) source
    (mInertiaQuotientEmbedding G field _ inf_le_right)
    (mInertiaQuotientEmbedding_injective G field _ inf_le_right)

/-- The second ordinary extension uses the actual quotient of the
base-and-field inertia and the existing embedding into E. -/
theorem ordinary_GE [IsCyclic E]
    [HasEnoughRootsOfUnity K (Nat.card (Inertia G field action W (baseFieldGroup G field) ⧸
      RadicalInInertia G field action W (baseFieldGroup G field)))]
    (source : ScopedCyclicExtensionSource K
      (Inertia G field action W (baseFieldGroup G field) ⧸
        RadicalInInertia G field action W (baseFieldGroup G field))) :
    Nonempty (LocalOrdinaryExtension G field W
      (rawNormalizerInertia G field action W ⊓ baseFieldGroup G field)) := by
  letI := embeddedG_normal G field action
  exact localOrdinaryExtension_of_cyclic_embedding G field action W
    (baseFieldGroup G field) (embeddedG_le_baseFieldGroup G field) source
    (fieldInertiaQuotientEmbedding G field action _ inf_le_right)
    (fieldInertiaQuotientEmbedding_injective G field action _ inf_le_right)

end ModularRep.PaperProofs.TypeBLocalOrdinaryExtensionSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
