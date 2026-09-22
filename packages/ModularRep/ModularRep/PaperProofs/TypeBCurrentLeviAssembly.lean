import ModularRep.PaperProofs.TypeBCurrentLeviFactorSelection
import ModularRep.PaperProofs.TypeBLeviRepresentativeAssembly
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers

/-!
# The same Levi character from the original factor representatives

This is the component/Clifford part of the accepted actual Levi representative
argument, with the standard-factor selector replaced by the constructed
type A, B2 and guarded principal Spin representatives. All character choices
are made in the proof. In particular, one element transports both the original
constituent and the original Levi character.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentLeviAssembly

open ModularRep FDRepSimpleClassKZero
open TypeBRegularLeviRationalCarriers TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLeviRepresentativeAssembly
open TypeBLeviRepresentativeClifford TypeBLeviRepresentativeField
open TypeBLemma47LeviApplication TypeBCharacteristicTwoConstituentSource
open TypeBCharacteristicTwoCorrespondenceSource TypeBCharacteristicTwoExtensionCarriers
open TypeBCharacteristicTwoCliffordKernel TypeBCharacteristicTwoCliffordApplication
open TypeBCharacteristicTwoGallagherSource TypeBCharacteristicTwoGallagherProduct
open TypeBRankThreeJordanPacketCarriers

variable {A E k K : Type} [Group A] [Group E] [Finite E] [IsCyclic E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (Frob : MulAut A) (Lbar : Subgroup A)
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable (leviStable : Lbar.map Frob.toMonoidHom = Lbar)
variable (field : FieldData Frob Lbar E)
variable (iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
variable (iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))
variable (iotaGamma : PrimeRegularRootEmbedding 2 k K (Gamma Frob Lbar))

/-- Primal geometry and standard source instances for a specified constituent.
The cycle indexing is permitted to depend on its actual orbit stabilizer. -/
structure ComponentInput (theta0 : IBr (rootN Frob Lbar iotaN)) where
  C : Type
  [finiteC : Fintype C]
  m : C → ℕ
  geometry : PrimalData Frob Lbar leviStable m
  presentation : Presentation geometry field iotaN theta0
  factors : TypeBCurrentLeviFactorSelection.RawFactorSources presentation

attribute [instance] ComponentInput.finiteC

/-- Uniform finite group Clifford inputs for the original literal chain.
GM, Theorem 1.7.15 supplies multiplicity freeness; Navarro, Corollaries
8.7 and 8.20 and Theorem 8.9 supply the stated one-way finite group principles. -/
structure CliffordInput where
  roots : RootAgreement (H Frob Lbar) (N Frob Lbar)
    (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN)
  iotaI : ∀ theta : IBr (rootN Frob Lbar iotaN),
    PrimeRegularRootEmbedding 2 k K
      (BrauerInertia (H Frob Lbar) (N Frob Lbar) (rootN Frob Lbar iotaN) theta)
  iotaA : ∀ theta : IBr (rootN Frob Lbar iotaN),
    PrimeRegularRootEmbedding 2 k K
      (AmbientInertia (N Frob Lbar) (rootN Frob Lbar iotaN) theta)
  roots_N_G : RootsAgree iotaGamma (rootN Frob Lbar iotaN)
  roots_A_G : ∀ theta, RootsAgree iotaGamma (iotaA theta)
  roots_N_A : ∀ theta, RootsAgree (iotaA theta) (rootN Frob Lbar iotaN)
  roots_I_A : ∀ theta, RootsAgree (iotaA theta) (iotaI theta)
  multiplicityFree : MultiplicityFreeRestriction (N Frob Lbar)
    iotaGamma (rootN Frob Lbar iotaN)
  above : ExistsAbovePrinciple k K
  homogeneous : HomogeneousCliffordPrinciple k K
  navarro87 : Navarro87Principle k K
  navarro89 : ∀ theta, Navarro89Source (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
    (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) theta (iotaI theta)
  navarro820 : Navarro820AbelianProductPrinciple k K

local instance quotientCommutative : IsMulCommutative (Gamma Frob Lbar ⧸ N Frob Lbar) :=
  quotientN_abelian Frob Lbar

/-- Both characters are transported by the same original paired-Levi element.
Component return and Clifford transfer construct the full chosen-field
factorization; it is not a field of either source record. -/
theorem same_y_representative
    (raw : CliffordInput Frob Lbar iotaL iotaN iotaGamma)
    (psi0 : IBr (rootH Frob Lbar iotaL))
    (theta0 : IBr (rootN Frob Lbar iotaN))
    (occurs0 : Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi0 theta0)
    (components : ComponentInput Frob Lbar leviStable field iotaN theta0) :
    letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
    letI := ambientBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN)
    letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
      field.fieldOnGamma field.H_stable
    ∃ (theta : IBr (rootN Frob Lbar iotaN)) (y : Gamma Frob Lbar)
        (psi : IBr (rootH Frob Lbar iotaL)),
      psi = y • psi0 ∧ theta = y • theta0 ∧
      Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
        (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi theta ∧
      Formalisation.SemidirectStabilizerFactors field.fieldOnGamma
        (field_ambient_semidirect_compatible (H Frob Lbar) (rootH Frob Lbar iotaL)
          field.fieldOnGamma field.H_stable) psi := by
  letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
  letI := ambientBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN)
  letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
    field.fieldOnGamma field.H_stable
  letI := fieldBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.N_stable
  obtain ⟨theta, selectedInOrbit, selectedFixed, _⟩ :=
    TypeBCurrentLeviFactorSelection.selected_constituent components.geometry field iotaN
      theta0 components.presentation components.factors
  obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp selectedInOrbit
  let psi : IBr (rootH Frob Lbar iotaL) := y • psi0
  have occurs : Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi theta := by
    rw [← hy]
    exact occurs_ambient (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) y psi0 theta0 occurs0
  have orbitEq := orbit_field_stabilizer_eq (N Frob Lbar) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.N_stable theta0 theta selectedInOrbit
  let EO := orbitFieldStabilizer (N Frob Lbar) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.N_stable theta
  let fieldO := field.fieldOnGamma.comp EO.subtype
  have hHO := fun e : EO => field.H_stable e.val
  have hNO := fun e : EO => field.N_stable e.val
  have thetaFixed : ∀ e : EO, (e : E) • theta = theta := by
    intro e
    have he : e.val ∈ orbitFieldStabilizer (N Frob Lbar) (rootN Frob Lbar iotaN)
        field.fieldOnGamma field.N_stable theta0 := by
      rw [← orbitEq]
      exact e.property
    exact selectedFixed ⟨e.val, he⟩
  have thetaFactorization :
      letI := fieldBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN) fieldO hNO
      Formalisation.SemidirectStabilizerFactors fieldO
        (field_ambient_semidirect_compatible (N Frob Lbar) (rootN Frob Lbar iotaN)
          fieldO hNO) theta := by
    intro x
    change x.left • ((x.right : E) • theta) = theta ↔
      x.left • theta = theta ∧ (x.right : E) • theta = theta
    rw [thetaFixed x.right]
    simp only [eq_self_iff_true, and_true]
  have localFactorization := representative_characteristic_two_clifford (E := EO)
    (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) iotaGamma
    (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi theta occurs
    (raw.iotaI theta) (raw.iotaA theta) raw.roots_N_G (raw.roots_A_G theta)
    raw.multiplicityFree raw.above raw.homogeneous raw.navarro87 (raw.navarro89 theta)
    raw.navarro820 (raw.roots_N_A theta) (raw.roots_I_A theta)
    fieldO hHO hNO thetaFactorization
  refine ⟨theta, y, psi, rfl, hy.symm, occurs, ?_⟩
  apply full_field_factorization (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
    (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.H_stable field.N_stable raw.roots raw.navarro87 psi theta occurs
  intro g e
  exact localFactorization ⟨g, e⟩

end ModularRep.PaperProofs.TypeBCurrentLeviAssembly



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
