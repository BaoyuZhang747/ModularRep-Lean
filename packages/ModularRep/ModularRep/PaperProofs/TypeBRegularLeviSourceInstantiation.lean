import ModularRep.PaperProofs.TypeBRegularLeviOrbitAssembly
import ModularRep.PaperProofs.TypeBRegularLeviCliffordBinding

/-!
# Current Lemma 4.5 on the original rational Levi subgroups

This endpoint joins the constructed rational product/action/orbit argument to
the literal normal chain, abelian quotient, effective quotient and specified
field action in the same geometric ambient point group. The generic endpoint
does not restrict an arbitrary regular embedding to the special Clifford model.

All algebraic interpretation remains explicitly conditional: PointGeometry
contains only lower point consequences of the specified regular embedding;
ComponentPointData binds the original component subgroups and Frobenius;
CentralLangSource is the exact specialized pointwise consequence, whose
connected closed centre and Steinberg hypotheses remain E2/U source matching.
No new formal algebraic predicate, orbit law, supported lift, image
surjectivity, effective exponent, or numbered conclusion is a source input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviSourceInstantiation

open TypeBRegularLeviRationalCarriers TypeBRegularLeviSupportedLift
open TypeBRegularLeviComponentPointSource TypeBRegularLeviCharacterActionAdapter
open TypeBRegularLeviOrbitLemma46Relative EvenFieldAssumption53Relative

variable {A : Type} [Group A] (Frob : MulAut A)

/-- Lower point consequences on one specified regular embedding.
E1/U: Geck--Malle Definition 1.7.1 and Remark 1.7.6(a);
Malle--Testerman Proposition 9.15/Table 9.2. Identifying these subgroups
with the intended connected algebraic groups remains explicit.
In particular no rational quotient or action-image conclusion occurs here. -/
structure PointGeometry where
  spin : Subgroup A
  levi : Subgroup A
  levi_le_spin : levi ≤ spin
  levi_stable : levi.map Frob.toMonoidHom = levi
  spin_stable : ∀ g ∈ spin, Frob g ∈ spin
  ambient_central : ∀ x : A, ∃ g ∈ spin, ∃ z ∈ Subgroup.center A, x = g * z
  central_spin_square : ∀ t : A, t ∈ spin → t ∈ Subgroup.center A → t ^ 2 = 1
  intersection : pairedLevi levi ⊓ spin ≤ levi

variable (geometry : PointGeometry Frob)

/-- The Frobenius used by the orbit proof is the actual restriction to Mbar. -/
abbrev pairedFrobenius :=
  TypeBRegularLeviCliffordBinding.frobeniusB Frob geometry.levi geometry.levi_stable

/-- Hbar is the actual derived subgroup inside that same Mbar. -/
abbrev derivedInside := TypeBRegularLeviCliffordBinding.H geometry.levi

theorem derived_stable :
    ∀ h ∈ derivedInside Frob geometry, pairedFrobenius Frob geometry h ∈ derivedInside Frob geometry :=
  TypeBRegularLeviCliffordBinding.geometricH_stable Frob geometry.levi geometry.levi_stable

variable {C : Type} (m : C → ℕ)
variable (components : ComponentPointData (pairedFrobenius Frob geometry)
  (derivedInside Frob geometry) (derived_stable Frob geometry) m)

/-- Every rational factor is a fixed subgroup of an original component
subgroup; its full-return map is computed from the original Frobenius. -/
abbrev factor (c : C) :=
  rationalFactor (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
    (derived_stable Frob geometry) m components c

variable (central : ∀ b : pairedLevi geometry.levi,
  ∃ h : derivedInside Frob geometry, ∃ z : Subgroup.center (pairedLevi geometry.levi),
    b = (h : pairedLevi geometry.levi) * z)

/-- Product identification starting on the original ambient rational L0. -/
def productEquiv : L0 Frob.toMonoidHom geometry.levi ≃* ((c : C) → factor Frob geometry m components c) :=
  TypeBRegularLeviOrbitAssembly.originalProduct
    (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
    (derived_stable Frob geometry) m components
    (TypeBRegularLeviCliffordBinding.rationalHEquivL0 Frob geometry.levi geometry.levi_stable)

/-- The constructed action, on the ORIGINAL M and L0 subgroups. -/
def conjugationAction :
    M Frob.toMonoidHom geometry.levi →* MulAut (L0 Frob.toMonoidHom geometry.levi) :=
  TypeBRegularLeviOrbitAssembly.originalAction
    (pairedFrobenius Frob geometry) (derivedInside Frob geometry) central
    (TypeBRegularLeviCliffordBinding.rationalHEquivL0 Frob geometry.levi geometry.levi_stable)
    (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob geometry.levi geometry.levi_stable)

/-- The transported action is literally original ambient conjugation;
the carrier/action interpretation is a proved point-value equality. -/
theorem conjugationAction_value (b : M Frob.toMonoidHom geometry.levi)
    (x : L0 Frob.toMonoidHom geometry.levi) :
    (conjugationAction Frob geometry central b x).1.1 = b.1.1 * x.1.1 * b.1.1⁻¹ := rfl

abbrev factorImage (c : C) :=
  TypeBRegularLeviOrbitAssembly.imageGroup
    (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
    (derived_stable Frob geometry) m components central c

def factorImageAction (c : C) :
    factorImage Frob geometry m components central c →*
      MulAut (factor Frob geometry m components c) :=
  TypeBRegularLeviOrbitAssembly.imageAction
    (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
    (derived_stable Frob geometry) m components central c

def productImageMap :
    M Frob.toMonoidHom geometry.levi →* ((c : C) → factorImage Frob geometry m components central c) :=
  TypeBRegularLeviOrbitAssembly.originalImageProduct
    (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
    (derived_stable Frob geometry) m components central
    (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob geometry.levi geometry.levi_stable)

section FiniteCharacters

variable [Fintype C] [Finite (fixedPoints Frob.toMonoidHom)]

local instance pairedFinite : Finite (fixedPoints (pairedFrobenius Frob geometry)) :=
  Finite.of_equiv (M Frob.toMonoidHom geometry.levi)
    (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob geometry.levi geometry.levi_stable).symm.toEquiv

local instance factorFinite (c : C) : Finite (factor Frob geometry m components c) :=
  TypeBRegularLeviOrbitAssembly.rationalFactor_finite
    (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
    (derived_stable Frob geometry) m components c

variable {ell : ℕ} {k K : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding ell k K (L0 Frob.toMonoidHom geometry.levi))
variable (factorRoot : ∀ c, PrimeRegularRootEmbedding ell k K (factor Frob geometry m components c))
variable (productSource : TypeBFiniteProductNaturality.ExternalProductData
  (factor Frob geometry m components)
  (iota.alongMulEquiv (productEquiv Frob geometry m components)) factorRoot)

/-- The actual character equivalence, using the prescribed L0 root. -/
def characterEquiv : IBr iota ≃ ((c : C) → IBr (factorRoot c)) :=
  TypeBRegularLeviOrbitAssembly.originalCharacters
    (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
    (derived_stable Frob geometry) m components
    (TypeBRegularLeviCliffordBinding.rationalHEquivL0 Frob geometry.levi geometry.levi_stable)
    iota factorRoot productSource

variable {E : Type} [Group E]
variable (field : E →* MulAut A)
variable (commutes : ∀ e x, Frob (field e x) = field e (Frob x))
variable (field_stable : ∀ e, geometry.levi.map (field e).toMonoidHom = geometry.levi)

include field_stable in
/-- Current Lemma 4.5, conditional on the stated original point sources.
All conclusions concern the same original L0/L/M, actual Brauer functions,
actual factor-image subgroups, actual effective quotient and field maps. -/
theorem regular_levi_orbits_source_instantiated
    (lang : CentralLangSource (pairedFrobenius Frob geometry)) :
    Nonempty (L0 Frob.toMonoidHom geometry.levi ≃* ((c : C) → factor Frob geometry m components c)) ∧
    Nonempty (IBr iota ≃ ((c : C) → IBr (factorRoot c))) ∧
    Function.Surjective (productImageMap Frob geometry m components central) ∧
    ((MulAut.congr (productEquiv Frob geometry m components)).toMonoidHom.comp
      (conjugationAction Frob geometry central)).range =
      (coordinateMulAut (factor Frob geometry m components)
        (fun c ↦ ↥(factorImage Frob geometry m components central c))
        (factorImageAction Frob geometry m components central)).range ∧
    (let _ := rightAutomorphismAction iota (conjugationAction Frob geometry central);
      ∀ base : IBr iota,
        characterEquiv Frob geometry m components iota factorRoot productSource '' MulAction.orbit
          (M Frob.toMonoidHom geometry.levi) base =
        {theta | ∀ c,
          let _ := rightAutomorphismAction (factorRoot c) (factorImageAction Frob geometry m components central c);
          theta c ∈ MulAction.orbit (factorImage Frob geometry m components central c)
            (characterEquiv Frob geometry m components iota factorRoot productSource base c)}) ∧
    L0 Frob.toMonoidHom geometry.levi ≤ L Frob.toMonoidHom geometry.levi ∧
    L Frob.toMonoidHom geometry.levi ≤ M Frob.toMonoidHom geometry.levi ∧
    ((L0 Frob.toMonoidHom geometry.levi).subgroupOf (L Frob.toMonoidHom geometry.levi)).Normal ∧
    ((L Frob.toMonoidHom geometry.levi).subgroupOf (M Frob.toMonoidHom geometry.levi)).Normal ∧
    (letI := L0_normal_M Frob.toMonoidHom geometry.levi;
      IsMulCommutative (M Frob.toMonoidHom geometry.levi ⧸
        (L0 Frob.toMonoidHom geometry.levi).subgroupOf (M Frob.toMonoidHom geometry.levi))) ∧
    (letI := effectiveKernel_normal_of_le_normalizer
        (M Frob.toMonoidHom geometry.levi) (L Frob.toMonoidHom geometry.levi)
        (L_le_M Frob.toMonoidHom geometry.levi)
        (rational_le_normalizer Frob.toMonoidHom (pairedLevi geometry.levi) geometry.levi
          (paired_le_Levi_normalizer geometry.levi));
      ∀ q : M Frob.toMonoidHom geometry.levi ⧸
        effectiveKernel (M Frob.toMonoidHom geometry.levi) (L Frob.toMonoidHom geometry.levi),
        q ^ 2 = 1) ∧
    (∀ e,
      (L0 Frob.toMonoidHom geometry.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = L0 Frob.toMonoidHom geometry.levi ∧
      (L Frob.toMonoidHom geometry.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = L Frob.toMonoidHom geometry.levi ∧
      (M Frob.toMonoidHom geometry.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = M Frob.toMonoidHom geometry.levi) := by
  refine ⟨⟨productEquiv Frob geometry m components⟩,
    ⟨characterEquiv Frob geometry m components iota factorRoot productSource⟩, ?_, ?_, ?_,
    L0_le_L Frob.toMonoidHom geometry.levi, L_le_M Frob.toMonoidHom geometry.levi,
    L0_normal_L Frob.toMonoidHom geometry.levi, L_normal_M Frob.toMonoidHom geometry.levi,
    M_quotient_L0_abelian Frob.toMonoidHom geometry.levi,
    effective_quotient_exponent_two Frob geometry.spin geometry.levi geometry.spin_stable
      geometry.ambient_central geometry.central_spin_square geometry.intersection, ?_⟩
  · exact TypeBRegularLeviOrbitAssembly.originalImageProduct_surjective
      (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
      (derived_stable Frob geometry) m components central
      (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob geometry.levi geometry.levi_stable) lang
  · exact TypeBRegularLeviOrbitAssembly.original_action_image
      (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
      (derived_stable Frob geometry) m components central
      (TypeBRegularLeviCliffordBinding.rationalHEquivL0 Frob geometry.levi geometry.levi_stable)
      (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob geometry.levi geometry.levi_stable) lang
  · dsimp only
    intro base
    exact TypeBRegularLeviOrbitAssembly.cartesian_character_orbit
      (pairedFrobenius Frob geometry) (derivedInside Frob geometry)
      (derived_stable Frob geometry) m components central
      (TypeBRegularLeviCliffordBinding.rationalHEquivL0 Frob geometry.levi geometry.levi_stable)
      (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob geometry.levi geometry.levi_stable)
      iota factorRoot productSource lang base
  · intro e
    exact field_preserves_chain Frob.toMonoidHom field commutes geometry.levi field_stable e

end FiniteCharacters

end ModularRep.PaperProofs.TypeBRegularLeviSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
