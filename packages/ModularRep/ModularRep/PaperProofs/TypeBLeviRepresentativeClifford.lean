import ModularRep.PaperProofs.TypeBCharacteristicTwoCorrespondenceSource
import ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherSource
import ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherProduct

/-!
# Multiplicity-free restriction and the Levi representative's inertia extension

This module supplies the deduction preceding the characteristic-two Clifford
lemma in the current Type B representative argument. All characters and maps
are on the literal finite group Gamma, its normal subgroup N, and the full
ambient inertia group Gamma_theta already used by the accepted lemma.

The new source boundary consists of three distinct statements. The actual
restriction to N is multiplicity free (the indicated instance of GM 1.7.15);
every irreducible character of N occurs under an ambient irreducible; and the
Clifford correspondent restricts homogeneously, with the SAME coefficient
that occurs in the ambient restriction. The last two are uniform finite group
principles with explicit coefficient fields and subgroup-root agreements.
The Clifford principle neither assumes multiplicity freeness nor concludes
extendibility. Source authentication and the actual regular-embedding instance
of the first statement remain E1/E2/U obligations.

The K deduction chooses an ambient character and its literal expansion,
proves that its nonzero theta coefficient equals one, and constructs the
extension. The final theorem uses this extension in the direct Gallagher
invariance proof of the revised Clifford lemma on the SAME psi, theta, chain,
and field action. This is its characteristic-two specialization; no effective
exponent, odd-square argument or separate tensor-product formula is needed.
No inertia extension or desired stabilizer factorization is a new source.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeClifford

open TypeBLemma47LeviApplication
open TypeBCharacteristicTwoCliffordKernel TypeBCharacteristicTwoCliffordApplication
open TypeBCharacteristicTwoConstituentSource TypeBCharacteristicTwoCorrespondenceSource
open TypeBCharacteristicTwoExtensionCarriers TypeBCharacteristicTwoGallagherSource
open TypeBCharacteristicTwoGallagherProduct
open ModularRep.ManuscriptVerification.CharacteristicTwoClifford

universe u

variable {Gamma k K : Type u} [Group Gamma] [Finite Gamma]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The literal nonnegative finite expansion on prime regular elements of N. -/
def RestrictionExpansion (N : Subgroup Gamma)
    (iotaGamma : PrimeRegularRootEmbedding 2 k K Gamma)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (Phi : IBr iotaGamma) (m : IBr iotaN →₀ ℕ) : Prop :=
  ∀ x : PrimeRegularElement (G := N) 2,
    Phi.1 (PrimeRegularElement.map N.subtype x) =
      m.sum (fun eta n => (n : K) * eta.1 x)

/-- The actual GM 1.7.15 input, stated for every literal restriction
expansion. Its regular-embedding applicability is a separate source obligation. -/
def MultiplicityFreeRestriction (N : Subgroup Gamma)
    (iotaGamma : PrimeRegularRootEmbedding 2 k K Gamma)
    (iotaN : PrimeRegularRootEmbedding 2 k K N) : Prop :=
  ∀ (Phi : IBr iotaGamma) (m : IBr iotaN →₀ ℕ),
    RestrictionExpansion N iotaGamma iotaN Phi m →
      ∀ theta : IBr iotaN, m theta ≤ 1

/-- Uniform existence of an ambient irreducible above a prescribed base
irreducible, using the existing literal restriction-support predicate. -/
def ExistsAbovePrinciple (k K : Type u)
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K] : Prop :=
  ∀ {Gamma : Type u} [Group Gamma] [Finite Gamma]
    (N : Subgroup Gamma) [N.Normal]
    (iotaGamma : PrimeRegularRootEmbedding 2 k K Gamma)
    (iotaN : PrimeRegularRootEmbedding 2 k K N),
    RootsAgree iotaGamma iotaN →
      ∀ theta : IBr iotaN, ∃ Phi : IBr iotaGamma,
        OccursAlong N.subtype iotaGamma iotaN Phi theta

/-- The homogeneous-restriction consequence of modular Clifford theory on
the full literal inertia group. The retained coefficient comes from the given
ambient expansion; neither multiplicity freeness nor extension is assumed. -/
def HomogeneousCliffordPrinciple (k K : Type u)
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K] : Prop :=
  ∀ {Gamma : Type u} [Group Gamma] [Finite Gamma]
    (N : Subgroup Gamma) [N.Normal]
    (iotaGamma : PrimeRegularRootEmbedding 2 k K Gamma)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN)
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta)),
    RootsAgree iotaGamma iotaN → RootsAgree iotaGamma iotaA →
    RootsAgree iotaA iotaN →
      ∀ (Phi : IBr iotaGamma) (m : IBr iotaN →₀ ℕ),
        m theta ≠ 0 → RestrictionExpansion N iotaGamma iotaN Phi m →
          ∃ eta : IBr iotaA, ∀ x : PrimeRegularElement (G := N) 2,
            eta.1 (PrimeRegularElement.map (baseInclusion N iotaN theta) x) =
              (m theta : K) * theta.1 x

/-- Multiplicity freeness makes the Clifford correspondent an actual
extension to Gamma_theta, with equality on the original N carrier. -/
theorem exists_ambient_extension_of_multiplicity_free
    (N : Subgroup Gamma) [N.Normal]
    (iotaGamma : PrimeRegularRootEmbedding 2 k K Gamma)
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta))
    (roots_N_G : RootsAgree iotaGamma iotaN)
    (roots_A_G : RootsAgree iotaGamma iotaA)
    (roots_N_A : RootsAgree iotaA iotaN)
    (multiplicityFree : MultiplicityFreeRestriction N iotaGamma iotaN)
    (above : ExistsAbovePrinciple k K)
    (clifford : HomogeneousCliffordPrinciple k K) :
    Nonempty (AmbientExtension N iotaN theta iotaA) := by
  obtain ⟨Phi, m, hm, hrestriction⟩ := above N iotaGamma iotaN roots_N_G theta
  have hexpansion : RestrictionExpansion N iotaGamma iotaN Phi m := hrestriction
  have hmOne : m theta = 1 :=
    Nat.le_antisymm (multiplicityFree Phi m hexpansion theta)
      (Nat.one_le_iff_ne_zero.mpr hm)
  obtain ⟨eta, heta⟩ := clifford N iotaGamma iotaN theta iotaA
    roots_N_G roots_A_G roots_N_A Phi m hm hexpansion
  refine ⟨⟨eta, ?_⟩⟩
  apply PrimeRegularClassFunction.ext
  intro x
  change eta.1 (PrimeRegularElement.map (baseInclusion N iotaN theta) x) = theta.1 x
  simpa only [hmOne, Nat.cast_one, one_mul] using heta x

/-- Characteristic-two specialization of the revised Clifford lemma.
The actual ambient inertia fixes the Gallagher product and hence its induced
character. Constituent adjustment then separates an arbitrary combined fixer.
Neither an effective exponent bound nor a tensor-action certificate is used. -/
theorem direct_characteristic_two_clifford
    {E : Type u} [Group E]
    (H N : Subgroup Gamma) [H.Normal] [N.Normal]
    [IsMulCommutative (Gamma ⧸ N)] (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (chosen : Occurs H N hNH iotaH iotaN psi theta)
    (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta))
    (extension : AmbientExtension N iotaN theta iotaA)
    (source87 : Navarro87Principle k K)
    (source89 : Navarro89Source H N hNH iotaH iotaN theta iotaI)
    (source820 : Navarro820AbelianProductPrinciple k K)
    (roots_N_A : RootsAgree iotaA iotaN)
    (roots_I_A : RootsAgree iotaA iotaI)
    (field : E →* MulAut Gamma)
    (hHstable : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
    (hNstable : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)
    (theta_factorization :
      letI := ambientBrauerAction N iotaN;
      letI := fieldBrauerAction N iotaN field hNstable;
      Formalisation.SemidirectStabilizerFactors field
        (field_ambient_semidirect_compatible N iotaN field hNstable) theta) :
    letI := ambientBrauerAction H iotaH;
    letI := fieldBrauerAction H iotaH field hHstable;
    Formalisation.SemidirectStabilizerFactors field
      (field_ambient_semidirect_compatible H iotaH field hHstable) psi := by
  letI : Fintype H := Fintype.ofFinite H
  letI := ambientBrauerAction H iotaH
  letI := ambientBrauerAction N iotaN
  letI := fieldBrauerAction H iotaH field hHstable
  letI := fieldBrauerAction N iotaN field hNstable
  letI := MulAction.compHom (IBr iotaI)
    (rightConjugationOnInertiaSubgroupHom H theta)
  obtain ⟨eta, heta⟩ := source89.exists_correspondent psi
    ((occurs_iff_occursAlong H N hNH iotaH iotaN psi theta).mp chosen)
  have product := source820 H N hNH iotaN theta iotaI iotaA
    source89.roots_N_I roots_N_A roots_I_A extension eta heta.1
  have inertiaFixes : ∀ a : AmbientInertia N iotaN theta, (a : Gamma) • psi = psi := by
    intro a
    have hetaFixed : a • eta = eta :=
      hasGallagherProduct_fixed H N iotaN theta iotaA extension.character iotaI eta product a
    have hrelated := inductionRelated_gamma H N hNH iotaH iotaN theta iotaI a psi eta heta
    have hrelatedFixed :
        InductionRelated H N hNH iotaH iotaN theta iotaI ((a : Gamma) • psi) eta := by
      simpa only [hetaFixed] using hrelated
    exact TypeBCharacteristicTwoInduction.BrauerInduces.unique
      (BrauerInertia H N iotaN theta) iotaI iotaH hrelatedFixed.2 heta.2
  let constituents := constituentOrbit H N hNH iotaH iotaN source89.roots_N_H
    field hHstable hNstable source87 psi theta chosen
  have thetaParts := productFactorization_of_semidirectStabilizerFactors
    N iotaN field hNstable theta theta_factorization
  change ∀ g : Gamma ⋊[field] E,
    g.left • (g.right • psi) = psi ↔
      g.left • psi = psi ∧ g.right • psi = psi
  intro g
  constructor
  · intro hfixed
    obtain ⟨h, htheta⟩ := adjust_to_fix_constituent H.subtype psi theta constituents hfixed
    have hparts := (thetaParts ((h : Gamma) * g.left) g.right).mp htheta
    have hambient : ((h : Gamma) * g.left) • psi = psi :=
      inertiaFixes ⟨(h : Gamma) * g.left, hparts.1⟩
    have hadjusted : ((h : Gamma) * g.left) • (g.right • psi) = psi := by
      rw [mul_smul, hfixed]
      exact subgroup_element_fixes_brauer_character H iotaH h psi
    have hfield : g.right • psi = psi :=
      (MulAction.injective ((h : Gamma) * g.left)) (hadjusted.trans hambient.symm)
    exact ⟨by simpa only [hfield] using hfixed, hfield⟩
  · rintro ⟨ha, he⟩
    rw [he, ha]

/-- The current representative's direct Clifford step. Its ambient
extension is derived from multiplicity freeness on the same selected theta.
This implements the characteristic-two use of the revised all-prime lemma. -/
theorem representative_characteristic_two_clifford
    {E : Type u} [Group E]
    (H N : Subgroup Gamma) [H.Normal] [N.Normal]
    [IsMulCommutative (Gamma ⧸ N)] (hNH : N ≤ H)
    (iotaGamma : PrimeRegularRootEmbedding 2 k K Gamma)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (chosen : Occurs H N hNH iotaH iotaN psi theta)
    (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta))
    (roots_N_G : RootsAgree iotaGamma iotaN)
    (roots_A_G : RootsAgree iotaGamma iotaA)
    (multiplicityFree : MultiplicityFreeRestriction N iotaGamma iotaN)
    (above : ExistsAbovePrinciple k K)
    (clifford : HomogeneousCliffordPrinciple k K)
    (source87 : Navarro87Principle k K)
    (source89 : Navarro89Source H N hNH iotaH iotaN theta iotaI)
    (source820 : Navarro820AbelianProductPrinciple k K)
    (roots_N_A : RootsAgree iotaA iotaN)
    (roots_I_A : RootsAgree iotaA iotaI)
    (field : E →* MulAut Gamma)
    (hHstable : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
    (hNstable : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)
    (theta_factorization :
      letI := ambientBrauerAction N iotaN;
      letI := fieldBrauerAction N iotaN field hNstable;
      Formalisation.SemidirectStabilizerFactors field
        (field_ambient_semidirect_compatible N iotaN field hNstable) theta) :
    letI := ambientBrauerAction H iotaH;
    letI := fieldBrauerAction H iotaH field hHstable;
    Formalisation.SemidirectStabilizerFactors field
      (field_ambient_semidirect_compatible H iotaH field hHstable) psi := by
  obtain ⟨extension⟩ := exists_ambient_extension_of_multiplicity_free
    N iotaGamma iotaN theta iotaA roots_N_G roots_A_G roots_N_A
    multiplicityFree above clifford
  exact direct_characteristic_two_clifford
    H N hNH iotaH iotaN psi theta chosen iotaI iotaA extension
    source87 source89 source820 roots_N_A roots_I_A
    field hHstable hNstable theta_factorization

end ModularRep.PaperProofs.TypeBLeviRepresentativeClifford


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
