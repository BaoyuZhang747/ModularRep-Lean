import ModularRep.PaperProofs.TypeBLeviRepresentativeSelection
import ModularRep.PaperProofs.TypeBLeviRepresentativeAssembly
import ModularRep.PaperProofs.TypeBLeviRepresentativeOriginalExtension
import ModularRep.BrauerCharacterSeparation

/-!
# The actual Levi representative deduction

Canonical manuscript `03b-type-b.tex`, SHA256
7ACE262433BB873A7FA2414AA53DF4594F696F98F1DECF4C59224FAEE50E4596,
lines 930--993, selected text SHA256
4C09AD955F7D4EA4A08DA63E9D50CB02FC11669D105A413EB2B017933E22888F,
stopping before Jordan decomposition. The historical
9FEDDE source used an exponent-two bound; the current deduction uses
direct Gallagher invariance and needs no such bound. For the prescribed
actual tilde-L orbit P in the union of the blocks e_s and an actual
constituent theta0 of psi0, this theorem constructs theta and ONE y that
transports both characters. It derives the actual constituent and block
covering, full field stabilizer factorization, field-fixer subgroup equality,
and an honest irreducible extension with the original root and restriction.

The actual rational Gamma, H and N are the canonical subgroup copies of
M, L and L0. Their original-value equivalences and root transports are in
Carriers. All component products, diagonal images, chain facts and
chosen-character facts are deduced here, not external target inputs.

The remaining external inputs are literal lower primal/field/return maps,
common adjoint projections and standard factor selectors, block catalogues,
root compatibility and the stated uniform GM/Navarro finite group facts.
Their exact E1/E2/U scope is recorded in this window's external-input audit;
the theorem does not assert an unconditional algebraic realization.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeApplication

open ModularRep FDRepSimpleClassKZero
open TypeBRegularLeviRationalCarriers TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLeviRepresentativeAssembly
open TypeBLeviRepresentativeTransport TypeBLeviRepresentativeClifford
open TypeBLeviRepresentativeField TypeBLemma47LeviApplication
open TypeBCharacteristicTwoConstituentSource TypeBCharacteristicTwoCorrespondenceSource
open TypeBCharacteristicTwoExtensionCarriers TypeBCharacteristicTwoCliffordKernel
open TypeBCharacteristicTwoCliffordApplication TypeBCharacteristicTwoGallagherSource
open TypeBCharacteristicTwoGallagherProduct

variable {A E k K : Type} [Group A] [Group E] [Finite E] [IsCyclic E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (Frob : MulAut A) (Lbar : Subgroup A)
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable (leviStable : Lbar.map Frob.toMonoidHom = Lbar)
variable {C : Type} [Fintype C] {m : C → ℕ}
variable (geometry : PrimalData Frob Lbar leviStable m)
variable (field : FieldData Frob Lbar E)
variable (originalRootH : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
variable (originalRootN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))
variable (iotaGamma : PrimeRegularRootEmbedding 2 k K (Gamma Frob Lbar))

/-- Restrict the same finite point action directly to the original L. -/
abbrev originalField :=
  TypeBLeviRepresentativeOriginalExtension.fieldOnOriginalL Frob Lbar field.sigma
    field.injective field.commutes field.sigma_levi field.sigma_centre
    field.fieldPoints field.generator field.generates field.generatorValue


noncomputable local instance finiteH : Fintype (H Frob Lbar) := Fintype.ofFinite (H Frob Lbar)
noncomputable local instance finiteNInH : Fintype (((N Frob Lbar)).subgroupOf (H Frob Lbar)) :=
  Fintype.ofFinite (((N Frob Lbar)).subgroupOf (H Frob Lbar))
local instance quotientCommutative : IsMulCommutative (Gamma Frob Lbar ⧸ (N Frob Lbar)) :=
  quotientN_abelian Frob Lbar
local instance ambientH : MulAction (Gamma Frob Lbar) (IBr (rootH Frob Lbar originalRootH)) := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar originalRootH)
local instance ambientN : MulAction (Gamma Frob Lbar) (IBr (rootN Frob Lbar originalRootN)) := ambientBrauerAction (N Frob Lbar) (rootN Frob Lbar originalRootN)

variable {BlockH BlockN : Type} [Fintype BlockH] [Fintype BlockN]
variable {idempotentH : BlockH → k[(H Frob Lbar)]}
variable {idempotentN : BlockN → k[((N Frob Lbar)).subgroupOf (H Frob Lbar)]}
variable (blocksH : BlockIdempotentDecomposition idempotentH)
variable (blocksN : BlockIdempotentDecomposition idempotentN)
variable (catalogueH : BlockCentralCharacterCatalogue (k := k) (G := (H Frob Lbar)) (Block := BlockH) blocksH)
variable (catalogueN : BlockCentralCharacterCatalogue (k := k)
  (G := ((N Frob Lbar)).subgroupOf (H Frob Lbar)) (Block := BlockN) blocksN)

/-- The full manuscript deduction on the actual rational Levi carriers.
The lower component and standard-group sources construct theta; no actual
factor/Levi selector, ambient extension, exponent or stabilizer conclusion
is a premise. The family of inertia roots and Navarro facts is uniform in
theta, so none is chosen for an unrelated representative. -/
theorem actual_levi_representative
    (roots_N_H : RootAgreement (H Frob Lbar) (N Frob Lbar) (rootH Frob Lbar originalRootH) (rootN Frob Lbar originalRootN))
    (fieldScope : SpathCoefficientField 2 k ((rootH Frob Lbar originalRootH)).prime)
    (covering : FixedRestrictionCovering (BlockH := BlockH) (BlockN := BlockN)
      (idempotentH := idempotentH) (idempotentN := idempotentN) (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootH Frob Lbar originalRootH) (rootN Frob Lbar originalRootN)
      blocksH blocksN (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (rootH Frob Lbar originalRootH)) (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (embeddedRoot (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootN Frob Lbar originalRootN))) catalogueH catalogueN roots_N_H fieldScope)
    (seriesBlocks : Set BlockH) (P : Set (IBr (rootH Frob Lbar originalRootH))) (psi0 : IBr (rootH Frob Lbar originalRootH))
    (prescribedOrbit : P = MulAction.orbit (Gamma Frob Lbar) psi0)
    (orbitInSeries : ∀ psi ∈ P,
      irreducibleBrauerCharacterBlock (rootH Frob Lbar originalRootH) (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (rootH Frob Lbar originalRootH)) blocksH psi ∈ seriesBlocks)
    (theta0 : IBr (rootN Frob Lbar originalRootN)) (occurs0 : Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootH Frob Lbar originalRootH) (rootN Frob Lbar originalRootN) psi0 theta0)
    (presentation : Presentation geometry field originalRootN theta0)
    (S Q J : C → Type) [∀ c, Group (S c)] [∀ c, Finite (S c)]
    [∀ c, Group (Q c)] [∀ c, Group (J c)]
    (standard : StandardData presentation S Q J)
    (iotaI : ∀ theta : IBr (rootN Frob Lbar originalRootN),
      PrimeRegularRootEmbedding 2 k K (BrauerInertia (H Frob Lbar) (N Frob Lbar) (rootN Frob Lbar originalRootN) theta))
    (iotaA : ∀ theta : IBr (rootN Frob Lbar originalRootN),
      PrimeRegularRootEmbedding 2 k K (AmbientInertia (N Frob Lbar) (rootN Frob Lbar originalRootN) theta))
    (roots_N_G : RootsAgree iotaGamma (rootN Frob Lbar originalRootN))
    (roots_A_G : ∀ theta, RootsAgree iotaGamma (iotaA theta))
    (roots_N_A : ∀ theta, RootsAgree (iotaA theta) (rootN Frob Lbar originalRootN))
    (roots_I_A : ∀ theta, RootsAgree (iotaA theta) (iotaI theta))
    (multiplicityFree : MultiplicityFreeRestriction (N Frob Lbar) iotaGamma (rootN Frob Lbar originalRootN))
    (above : ExistsAbovePrinciple k K)
    (homogeneousClifford : HomogeneousCliffordPrinciple k K)
    (source87 : Navarro87Principle k K)
    (source89 : ∀ theta, Navarro89Source (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootH Frob Lbar originalRootH) (rootN Frob Lbar originalRootN) theta (iotaI theta))
    (source820 : Navarro820AbelianProductPrinciple k K)
    (source812 : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k) :
    letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar originalRootH) field.fieldOnGamma field.H_stable;
    ∃ (theta : IBr (rootN Frob Lbar originalRootN)) (y : Gamma Frob Lbar) (psi : IBr (rootH Frob Lbar originalRootH)),
      psi = y • psi0 ∧ theta = y • theta0 ∧
      psi ∈ P ∧
      irreducibleBrauerCharacterBlock (rootH Frob Lbar originalRootH) (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (rootH Frob Lbar originalRootH)) blocksH psi ∈ seriesBlocks ∧
      Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootH Frob Lbar originalRootH) (rootN Frob Lbar originalRootN) psi theta ∧
      CentralCharacterCovers (((N Frob Lbar)).subgroupOf (H Frob Lbar))
        (catalogueH.centralCharacter
          (irreducibleBrauerCharacterBlock (rootH Frob Lbar originalRootH) (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (rootH Frob Lbar originalRootH)) blocksH psi))
        (catalogueN.centralCharacter
          (irreducibleBrauerCharacterBlock (embeddedRoot (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootN Frob Lbar originalRootN))
            (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (embeddedRoot (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootN Frob Lbar originalRootN))) blocksN (embeddedCharacter (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootN Frob Lbar originalRootN) theta))) ∧
      Formalisation.SemidirectStabilizerFactors field.fieldOnGamma
        (field_ambient_semidirect_compatible (H Frob Lbar) (rootH Frob Lbar originalRootH) field.fieldOnGamma field.H_stable) psi ∧
      (fieldStabilizer (rootH Frob Lbar originalRootH)
        ((restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable).comp
          (orbitFieldStabilizer (N Frob Lbar) (rootN Frob Lbar originalRootN) field.fieldOnGamma field.N_stable theta0).subtype) psi).map
          (orbitFieldStabilizer (N Frob Lbar) (rootN Frob Lbar originalRootN) field.fieldOnGamma field.N_stable theta0).subtype =
        fieldStabilizer (rootH Frob Lbar originalRootH) (restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable) psi ∧
      ∃ originalPsi : IBr originalRootH,
        IrreducibleBrauerCharacter.equivAlongMulEquiv originalRootH
          (originalLEquiv Frob Lbar) originalPsi = psi ∧
        fieldStabilizer originalRootH (originalField Frob Lbar field) originalPsi =
          fieldStabilizer (rootH Frob Lbar originalRootH) (restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable) psi ∧
        ∃ W : FDRep k (L Frob.toMonoidHom Lbar),
          Representation.IsIrreducible W.ρ ∧
          originalPsi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ originalRootH ∧
          ∃ rho : Representation k
            (FieldSemidirect originalRootH (originalField Frob Lbar field) originalPsi) W,
            Representation.IsIrreducible rho ∧
            Nonempty (Representation.Equiv
              (rho.pullback (SemidirectProduct.inl : L Frob.toMonoidHom Lbar →*
                FieldSemidirect originalRootH (originalField Frob Lbar field) originalPsi)) W.ρ) := by
  letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar originalRootH) field.fieldOnGamma field.H_stable
  letI := fieldBrauerAction (N Frob Lbar) (rootN Frob Lbar originalRootN) field.fieldOnGamma field.N_stable
  obtain ⟨theta, selectedInOrbit, selectedFixed, _⟩ :=
    selected_constituent geometry field originalRootN theta0 presentation S Q J standard
  have fixed : ∀ e : orbitFieldStabilizer (N Frob Lbar) (rootN Frob Lbar originalRootN) field.fieldOnGamma field.N_stable theta0,
      (e : E) • theta = theta := by
    intro e
    exact selectedFixed e
  obtain ⟨y, psi, hpsi, htheta, hinP, hinSeries, hoccurs, hcovers, hfull, himage, _⟩ :=
    assemble_prescribed_representative (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) iotaGamma (rootH Frob Lbar originalRootH) (rootN Frob Lbar originalRootN)
    field.fieldOnGamma field.H_stable field.N_stable
    blocksH blocksN (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (rootH Frob Lbar originalRootH)) (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (embeddedRoot (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) (rootN Frob Lbar originalRootN))) catalogueH catalogueN roots_N_H fieldScope covering
    seriesBlocks P psi0 prescribedOrbit orbitInSeries theta0 theta occurs0
    selectedInOrbit fixed (iotaI theta) (iotaA theta) roots_N_G (roots_A_G theta)
    (roots_N_A theta) (roots_I_A theta) multiplicityFree above homogeneousClifford
    source87 (source89 theta) source820 source812
  exact ⟨theta, y, psi, hpsi, htheta, hinP, hinSeries, hoccurs, hcovers, hfull, himage,
    TypeBLeviRepresentativeOriginalExtension.honest_original_field_extension
      Frob Lbar field.sigma field.injective field.commutes field.sigma_levi field.sigma_centre
      field.fieldPoints field.generator field.generates field.generatorValue
      originalRootH psi source812⟩

end ModularRep.PaperProofs.TypeBLeviRepresentativeApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
