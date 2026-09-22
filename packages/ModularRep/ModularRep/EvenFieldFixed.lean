import ModularRep.OddQuasiIsolation
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Kernel deductions for the even-field fixed-point lemma

This file retains only the deductions in manuscript Lemma 3.6 that are
independent of the deep Deligne--Lusztig, rational-Levi, extension, and
Clifford-theoretic inputs.  The former aggregate `ExternalData` theorem was
removed because several of its fields supplied manuscript deductions rather
than source-shaped published inputs.
-/

namespace ModularRep.ManuscriptVerification.EvenFieldFixed

/-- Manuscript lines 307--310, after rational-series disjointness has supplied
the displayed conjugacy and the two semantic order predicates have been
translated to `IsPrimeRegular` and a prime-power annihilating exponent. -/
theorem conjugate_primePower_primeRegular_eq_one
    {G : Type*} [Group G] {ell : ℕ} {s t x : G}
    (hconj : t = x * s * x⁻¹)
    (hs : IsPrimeRegular ell s)
    (ht : ∃ a : ℕ, t ^ (ell ^ a) = 1) :
    s = 1 ∧ t = 1 := by
  have htreg : IsPrimeRegular ell t := by
    rw [hconj]
    exact hs.conj x
  obtain ⟨a, htpow⟩ := ht
  have htregPow : IsPrimeRegular (ell ^ a) t := by
    exact htreg.pow_right a
  have htOne : t = 1 := htregPow.eq_one_of_pow_eq_one htpow
  have hsOne : s = 1 := by
    rw [htOne] at hconj
    have : x * s * x⁻¹ = 1 := hconj.symm
    simpa [mul_assoc] using congrArg (fun z : G => x⁻¹ * z * x) this
  exact ⟨hsOne, htOne⟩

/-- Once two rational-series labels of one character are known to be
conjugate, an `ell`-regular label and an `ell`-element label must both be the
identity. -/
theorem common_series_primePower_primeRegular_is_unipotent
    {G Character : Type*} [Group G] {ell : ℕ}
    (Series : Character → G → Prop)
    (seriesDisjoint : ∀ {chi : Character} {s t : G},
      Series chi s → Series chi t → ∃ x : G, t = x * s * x⁻¹)
    {chi : Character} {s t : G}
    (hsSeries : Series chi s) (htSeries : Series chi t)
    (hs : IsPrimeRegular ell s)
    (ht : ∃ a : ℕ, t ^ (ell ^ a) = 1) :
    Series chi 1 := by
  obtain ⟨x, hconj⟩ := seriesDisjoint hsSeries htSeries
  have hlabels := conjugate_primePower_primeRegular_eq_one hconj hs ht
  simpa [hlabels.2] using htSeries

/-- Field invariance of unipotent characters completes the ordinary-character
half after the label collapse. -/
theorem common_series_character_fixed
    {G Character : Type*} [Group G] {ell : ℕ}
    (Series : Character → G → Prop)
    (sigma : Character → Character)
    (seriesDisjoint : ∀ {chi : Character} {s t : G},
      Series chi s → Series chi t → ∃ x : G, t = x * s * x⁻¹)
    (fieldFixesUnipotent : ∀ chi, Series chi 1 → sigma chi = chi)
    {chi : Character} {s t : G}
    (hsSeries : Series chi s) (htSeries : Series chi t)
    (hs : IsPrimeRegular ell s)
    (ht : ∃ a : ℕ, t ^ (ell ^ a) = 1) :
    sigma chi = chi := by
  apply fieldFixesUnipotent chi
  exact common_series_primePower_primeRegular_is_unipotent
    Series seriesDisjoint hsSeries htSeries hs ht

/-- Transformations differing by an inner action induce the same orbit. -/
theorem inner_twist_fixed_implies_orbit_fixed
    {G X : Type*} [Group G] [MulAction G X]
    (sigma : X → X) (h : G) (x : X)
    (hfixed : h • sigma x = x) :
    MulAction.orbit G (sigma x) = MulAction.orbit G x := by
  rw [MulAction.orbit_eq_iff]
  refine ⟨h⁻¹, ?_⟩
  calc
    h⁻¹ • x = h⁻¹ • (h • sigma x) :=
      congrArg (fun y => h⁻¹ • y) hfixed.symm
    _ = sigma x := by simp

/-- The actual orbit type used on the generic-weight side. -/
abbrev WeightOrbit (H WeightRepresentative : Type*)
    [Group H] [MulAction H WeightRepresentative] :=
  MulAction.orbitRel.Quotient H WeightRepresentative

/-- Pointwise fixation by every element of an automorphism-indexing type. -/
def PointwiseFixed {Automorphism X : Type*}
    (action : Automorphism → X → X) (S : Set X) : Prop :=
  ∀ a x, x ∈ S → action a x = x

/-- The representative and local character supplied by the definition of a
generic weight, with the ambient orbit recorded explicitly. -/
structure GenericWeightRepresentative
    {H WeightRepresentative LocalCharacter : Type*}
    [Group H] [MulAction H WeightRepresentative]
    (GenericLocal : WeightRepresentative → LocalCharacter → Prop)
    (omega : WeightOrbit H WeightRepresentative) where
  representative : WeightRepresentative
  represents :
    (Quotient.mk'' representative : WeightOrbit H WeightRepresentative) = omega
  localCharacter : LocalCharacter
  isGenericLocal : GenericLocal representative localCharacter

end ModularRep.ManuscriptVerification.EvenFieldFixed


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
