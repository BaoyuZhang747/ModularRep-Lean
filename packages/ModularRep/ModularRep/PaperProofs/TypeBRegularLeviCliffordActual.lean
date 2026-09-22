import ModularRep.PaperProofs.TypeBRegularLeviSourceInstantiation

/-!
# Current regular-Levi endpoint on the actual Clifford and Spin carriers

`pointGeometry` contains no new source information: it is constructed from
the already displayed Clifford fixed-point source and Levi point data.
The prescribed Brauer root starts on the literal finite inverse image of
the derived Levi under the same Clifford inclusion.  Its root on geometric
rational points is the canonical transport through that inclusion.

This is the actual Clifford specialization of the generic regular-embedding
endpoint.  It does not identify every regular embedding with this one.
All E1/E2/U interpretation obligations of the constituent sources remain:
algebraic Levi and component recognition, Clifford fixed-range descent,
geometric central decomposition, connected-centre Lang and external-product
source authentication.  No supported lift or orbit conclusion is an input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviCliffordActual

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBRegularLeviCliffordBinding TypeBRegularLeviSourceInstantiation
open TypeBRegularLeviSupportedLift TypeBRegularLeviComponentPointSource
open TypeBRegularLeviCharacterActionAdapter TypeBRegularLeviOrbitLemma46Relative
open EvenFieldAssumption53Relative

variable (n p f : ℕ) (F Kbar : Type)
variable [Field F] [Finite F] [CharP F p] [Field Kbar] [Algebra F Kbar]
variable (N : NormSource n F) (Nbar : NormSource n Kbar)
variable (Frob : MulAut (SpecialClifford n Kbar))
variable (S : CliffordFixedPointSource n p f F Kbar N Nbar Frob)
variable (P : LeviPointData n Kbar Nbar Frob)

/-- The generic lower point record is filled from the SAME actual Spin
norm kernel, Clifford Frobenius and Levi point data. -/
abbrev pointGeometry : PointGeometry Frob where
  spin := SpinSubgroup n Kbar Nbar
  levi := P.levi
  levi_le_spin := P.levi_le_spin
  levi_stable := P.frobenius_stable
  spin_stable := geometricSpin_frobenius_stable n p f F Kbar N Nbar Frob S
  ambient_central := P.central_decomposition
  central_spin_square := P.central_spin_square
  intersection := P.intersection.le



@[simp] theorem pointGeometry_spin : (pointGeometry n p f F Kbar N Nbar Frob S P).spin = SpinSubgroup n Kbar Nbar := rfl
@[simp] theorem pointGeometry_levi : (pointGeometry n p f F Kbar N Nbar Frob S P).levi = P.levi := rfl

/-- The finite paired-Levi carrier is exactly the base-change inverse image. -/
def finiteCarrierEquivM : finiteM n p f F Kbar N Nbar Frob S P ≃*
    M Frob.toMonoidHom P.levi :=
  finiteSubgroupEquiv n p f F Kbar N Nbar Frob S (pairedLevi P.levi)

def finiteCarrierEquivL : finiteL n p f F Kbar N Nbar Frob S P ≃*
    L Frob.toMonoidHom P.levi :=
  finiteSubgroupEquiv n p f F Kbar N Nbar Frob S P.levi

def finiteCarrierEquivL0 : finiteL0 n p f F Kbar N Nbar Frob S P ≃*
    L0 Frob.toMonoidHom P.levi :=
  finiteSubgroupEquiv n p f F Kbar N Nbar Frob S (derivedLevi P.levi)

@[simp] theorem finiteCarrierEquivM_value
    (x : finiteM n p f F Kbar N Nbar Frob S P) :
    (finiteCarrierEquivM n p f F Kbar N Nbar Frob S P x).1.1 = S.inclusion x.1 := rfl

@[simp] theorem finiteCarrierEquivL_value
    (x : finiteL n p f F Kbar N Nbar Frob S P) :
    (finiteCarrierEquivL n p f F Kbar N Nbar Frob S P x).1.1 = S.inclusion x.1 := rfl

@[simp] theorem finiteCarrierEquivL0_value
    (x : finiteL0 n p f F Kbar N Nbar Frob S P) :
    (finiteCarrierEquivL0 n p f F Kbar N Nbar Frob S P x).1.1 = S.inclusion x.1 := rfl

/-- The actual finite derived Levi is included in the SAME norm-kernel Spin. -/
def finiteL0ToSpin : finiteL0 n p f F Kbar N Nbar Frob S P →* Spin n F N where
  toFun x := ⟨x.1, finiteL_le_spin n p f F Kbar N Nbar Frob S P
    (finiteL0_le_finiteL n p f F Kbar N Nbar Frob S P x.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem finiteL0ToSpin_value
    (x : finiteL0 n p f F Kbar N Nbar Frob S P) :
    (finiteL0ToSpin n p f F Kbar N Nbar Frob S P x).1 = x.1 := rfl

variable [finiteClifford : Finite (SpecialClifford n F)]
variable [finiteAmbient : Finite (fixedPoints Frob.toMonoidHom)]

variable {C : Type} [Fintype C] (m : C → ℕ)
variable (components : ComponentPointData (pairedFrobenius Frob (pointGeometry n p f F Kbar N Nbar Frob S P))
  (derivedInside Frob (pointGeometry n p f F Kbar N Nbar Frob S P)) (derived_stable Frob (pointGeometry n p f F Kbar N Nbar Frob S P)) m)

local instance finiteFactor (c : C) : Finite (factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components c) := by
  letI : Finite (fixedPoints (pairedFrobenius Frob
      (pointGeometry n p f F Kbar N Nbar Frob S P))) :=
    Finite.of_equiv (M Frob.toMonoidHom P.levi)
      (fixedBEquivM Frob P.levi P.frobenius_stable).symm.toEquiv
  exact TypeBRegularLeviOrbitAssembly.rationalFactor_finite
    (pairedFrobenius Frob (pointGeometry n p f F Kbar N Nbar Frob S P)) (derivedInside Frob (pointGeometry n p f F Kbar N Nbar Frob S P))
    (derived_stable Frob (pointGeometry n p f F Kbar N Nbar Frob S P)) m components c

variable (central : ∀ b : pairedLevi P.levi,
  ∃ h : derivedInside Frob (pointGeometry n p f F Kbar N Nbar Frob S P), ∃ z : Subgroup.center (pairedLevi P.levi),
    b = h.1 * z.1)

variable {ell : ℕ} {k K : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable (finiteRoot : PrimeRegularRootEmbedding ell k K
  (finiteL0 n p f F Kbar N Nbar Frob S P))

/-- The root on rational geometric L0 is determined by the prescribed root
on its actual finite Clifford inverse image; no independent root is chosen. -/
abbrev rationalRoot : PrimeRegularRootEmbedding ell k K (L0 Frob.toMonoidHom P.levi) :=
  finiteRoot.alongMulEquiv (finiteCarrierEquivL0 n p f F Kbar N Nbar Frob S P)



/-- Canonical transport of actual finite Brauer characters through the same
group and root identification used by the regular-Levi endpoint. -/
def finiteCharacterEquiv : IBr finiteRoot ≃ IBr (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv finiteRoot
    (finiteCarrierEquivL0 n p f F Kbar N Nbar Frob S P)

variable (factorRoot : ∀ c, PrimeRegularRootEmbedding ell k K (factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components c))
variable (productSource : TypeBFiniteProductNaturality.ExternalProductData
  (factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)
  ((rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot).alongMulEquiv (productEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)) factorRoot)

variable {E : Type} [Group E]
variable (field : E →* MulAut (SpecialClifford n Kbar))
variable (commutes : ∀ e x, Frob (field e x) = field e (Frob x))
variable (field_stable : ∀ e, P.levi.map (field e).toMonoidHom = P.levi)

include field_stable in
/-- The full twelve-part regular-Levi endpoint on the literal Clifford/Spin
specialization, with a prescribed finite-carrier Brauer root.  The source
boundary is exactly the lower input boundary of the generic endpoint. -/
theorem regular_levi_orbits_actual_of_finite
    (lang : CentralLangSource (pairedFrobenius Frob (pointGeometry n p f F Kbar N Nbar Frob S P))) :
    Nonempty (L0 Frob.toMonoidHom P.levi ≃* ((c : C) → factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components c)) ∧
    Nonempty (IBr (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) ≃ ((c : C) → IBr (factorRoot c))) ∧
    Function.Surjective (productImageMap Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central) ∧
    ((MulAut.congr (productEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)).toMonoidHom.comp
      (conjugationAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) central)).range =
      (coordinateMulAut (factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)
        (fun c ↦ ↥(factorImage Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central c))
        (factorImageAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central)).range ∧
    (let _ := rightAutomorphismAction (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) (conjugationAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) central);
      ∀ base : IBr (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot),
        characterEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) factorRoot productSource '' MulAction.orbit
          (M Frob.toMonoidHom P.levi) base =
        {theta | ∀ c,
          let _ := rightAutomorphismAction (factorRoot c) (factorImageAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central c);
          theta c ∈ MulAction.orbit (factorImage Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central c)
            (characterEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) factorRoot productSource base c)}) ∧
    L0 Frob.toMonoidHom P.levi ≤ L Frob.toMonoidHom P.levi ∧
    L Frob.toMonoidHom P.levi ≤ M Frob.toMonoidHom P.levi ∧
    ((L0 Frob.toMonoidHom P.levi).subgroupOf (L Frob.toMonoidHom P.levi)).Normal ∧
    ((L Frob.toMonoidHom P.levi).subgroupOf (M Frob.toMonoidHom P.levi)).Normal ∧
    (letI := L0_normal_M Frob.toMonoidHom P.levi;
      IsMulCommutative (M Frob.toMonoidHom P.levi ⧸
        (L0 Frob.toMonoidHom P.levi).subgroupOf (M Frob.toMonoidHom P.levi))) ∧
    (letI := effectiveKernel_normal_of_le_normalizer
        (M Frob.toMonoidHom P.levi) (L Frob.toMonoidHom P.levi)
        (L_le_M Frob.toMonoidHom P.levi)
        (rational_le_normalizer Frob.toMonoidHom (pairedLevi P.levi) P.levi
          (paired_le_Levi_normalizer P.levi));
      ∀ q : M Frob.toMonoidHom P.levi ⧸
        effectiveKernel (M Frob.toMonoidHom P.levi) (L Frob.toMonoidHom P.levi), q ^ 2 = 1) ∧
    (∀ e,
      (L0 Frob.toMonoidHom P.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = L0 Frob.toMonoidHom P.levi ∧
      (L Frob.toMonoidHom P.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = L Frob.toMonoidHom P.levi ∧
      (M Frob.toMonoidHom P.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = M Frob.toMonoidHom P.levi) := by
  exact regular_levi_orbits_source_instantiated Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central
    (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) factorRoot productSource field commutes field_stable lang



include field_stable in
omit finiteClifford finiteAmbient in
/-- The source-specialized endpoint derives both required finiteness
instances from the existing finite Clifford certificate.  Thus the final
statement has no independently assumed finite rational ambient group. -/
theorem regular_levi_orbits_actual
    (finite : FiniteCliffordSource n F)
    (lang : CentralLangSource (pairedFrobenius Frob
      (pointGeometry n p f F Kbar N Nbar Frob S P))) :
    letI := specialClifford_finite n F finite;
    letI := geometric_fixedPoints_finite n p f F Kbar N Nbar Frob S finite;
    ∀ (finiteRoot : PrimeRegularRootEmbedding ell k K
        (finiteL0 n p f F Kbar N Nbar Frob S P))
      (factorRoot : ∀ c, PrimeRegularRootEmbedding ell k K
        (factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components c))
      (productSource : TypeBFiniteProductNaturality.ExternalProductData
        (factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)
        ((rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot).alongMulEquiv
          (productEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)) factorRoot),
    Nonempty (L0 Frob.toMonoidHom P.levi ≃* ((c : C) → factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components c)) ∧
    Nonempty (IBr (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) ≃ ((c : C) → IBr (factorRoot c))) ∧
    Function.Surjective (productImageMap Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central) ∧
    ((MulAut.congr (productEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)).toMonoidHom.comp
      (conjugationAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) central)).range =
      (coordinateMulAut (factor Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components)
        (fun c ↦ ↥(factorImage Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central c))
        (factorImageAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central)).range ∧
    (let _ := rightAutomorphismAction (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) (conjugationAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) central);
      ∀ base : IBr (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot),
        characterEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) factorRoot productSource '' MulAction.orbit
          (M Frob.toMonoidHom P.levi) base =
        {theta | ∀ c,
          let _ := rightAutomorphismAction (factorRoot c) (factorImageAction Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central c);
          theta c ∈ MulAction.orbit (factorImage Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components central c)
            (characterEquiv Frob (pointGeometry n p f F Kbar N Nbar Frob S P) m components (rationalRoot n p f F Kbar N Nbar Frob S P finiteRoot) factorRoot productSource base c)}) ∧
    L0 Frob.toMonoidHom P.levi ≤ L Frob.toMonoidHom P.levi ∧
    L Frob.toMonoidHom P.levi ≤ M Frob.toMonoidHom P.levi ∧
    ((L0 Frob.toMonoidHom P.levi).subgroupOf (L Frob.toMonoidHom P.levi)).Normal ∧
    ((L Frob.toMonoidHom P.levi).subgroupOf (M Frob.toMonoidHom P.levi)).Normal ∧
    (letI := L0_normal_M Frob.toMonoidHom P.levi;
      IsMulCommutative (M Frob.toMonoidHom P.levi ⧸
        (L0 Frob.toMonoidHom P.levi).subgroupOf (M Frob.toMonoidHom P.levi))) ∧
    (letI := effectiveKernel_normal_of_le_normalizer
        (M Frob.toMonoidHom P.levi) (L Frob.toMonoidHom P.levi)
        (L_le_M Frob.toMonoidHom P.levi)
        (rational_le_normalizer Frob.toMonoidHom (pairedLevi P.levi) P.levi
          (paired_le_Levi_normalizer P.levi));
      ∀ q : M Frob.toMonoidHom P.levi ⧸
        effectiveKernel (M Frob.toMonoidHom P.levi) (L Frob.toMonoidHom P.levi), q ^ 2 = 1) ∧
    (∀ e,
      (L0 Frob.toMonoidHom P.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = L0 Frob.toMonoidHom P.levi ∧
      (L Frob.toMonoidHom P.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = L Frob.toMonoidHom P.levi ∧
      (M Frob.toMonoidHom P.levi).map
          (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom = M Frob.toMonoidHom P.levi) := by
  letI := specialClifford_finite n F finite
  letI := geometric_fixedPoints_finite n p f F Kbar N Nbar Frob S finite
  dsimp only
  intro finiteRoot factorRoot productSource
  exact regular_levi_orbits_actual_of_finite n p f F Kbar N Nbar Frob S P
    m components central finiteRoot factorRoot productSource field commutes field_stable lang

end ModularRep.PaperProofs.TypeBRegularLeviCliffordActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
