import ModularRep.PaperProofs.TypeBInertiaHallSource
import ModularRep.PaperProofs.TypeBSpinRestrictionConstituent
import ModularRep.PaperProofs.OddGFactorizationLemma312ActualExtension
import ModularRep.BrauerCharacterExtensionBridge
import ModularRep.OrdinaryCharacterCyclicExtensionBridge

/-!
# Cyclic extension on the actual Type B inertia groups

The source input is the universally quantified representation-level cyclic
extension theorem, Navarro (8.12), p. 163. The field is algebraically closed
of characteristic ell. The fixed function-valued Brauer character is realized
on the literal Spin subgroup, then transported along the canonical inclusion
into its inertia. Character invariance and cyclicity of the inertia quotient
are proved. No extension of a Type B character is a source premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCyclicExtensionSource

open ModularRep TypeBCliffordCarriers TypeBInertiaHallSource
open CyclicOuterLemma37Concrete
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open Formalisation

/-- The quotient of any subgroup by its intersection with a normal subgroup
embeds in the original quotient. Thus cyclicity restricts to the ACTUAL
inertia quotient. -/
theorem subgroup_quotient_cyclic {M : Type} [Group M]
    (G I : Subgroup M) [G.Normal] [IsCyclic (M ⧸ G)] :
    IsCyclic (I ⧸ G.subgroupOf I) := by
  let q : I →* M ⧸ G := (QuotientGroup.mk' G).comp I.subtype
  have hker : q.ker = G.subgroupOf I := by
    ext x
    change (QuotientGroup.mk' G x.1 = 1) ↔ x.1 ∈ G
    exact QuotientGroup.eq_one_iff x.1
  let e := QuotientGroup.quotientMulEquivOfEq hker.symm
  exact isCyclic_of_injective ((QuotientGroup.kerLift q).comp e.toMonoidHom)
    ((QuotientGroup.kerLift_injective q).comp e.injective)

/-- The ordinary counterpart of the local quotient-tower deduction.
Isaacs, Corollary 11.22, p. 186, is used only through the universally
quantified representation extension principle. The output is an ordinary
irreducible character on the actual quotient D/Q, with literal values on
the image of the base normalizer. Cyclicity after removing Q is proved. -/
theorem ordinary_extension_over_quotient_tower
    {D C K : Type} [Group D] [Finite D] [Group C] [IsCyclic C]
    [Field K] [CharZero K] [IsAlgClosed K]
    (principle : Representation.CyclicExtensionPrinciple.{0, 0, 0} K)
    (Q B : Subgroup D) [Q.Normal] [B.Normal] (hQB : Q ≤ B)
    (embedding : (D ⧸ B) →* C) (injective : Function.Injective embedding)
    (theta : OrdinaryIrreducibleCharacter.Irr K (B.map (QuotientGroup.mk' Q)))
    (fixed : ∀ d : D ⧸ Q, ∀ x : B.map (QuotientGroup.mk' Q),
      theta (MulAut.conjNormal d x) = theta x) :
    ∃ thetaHat : OrdinaryIrreducibleCharacter.Irr K (D ⧸ Q),
      ∀ x : B.map (QuotientGroup.mk' Q), thetaHat x.1 = theta x := by
  exact OrdinaryIrreducibleCharacter.exists_extension_of_fixed_cyclic_quotient
    (B.map (QuotientGroup.mk' Q)) principle theta
    (isCyclic_quotient_tower_of_embedding Q B hQB embedding injective) fixed

variable {n p f ell : ℕ} {F k K : Type}
variable [Field F] [Finite F] [Field k] [Field K]
variable [CharP k ell] [IsAlgClosed k] [CharZero K]
variable (N : NormSource n F) [Finite (SpecialClifford n F)]
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- The literal copy of Spin inside the actual special Clifford inertia. -/
def spinInInertia (phi : IBr iota) : Subgroup (brauerInertia N iota phi) :=
  (SpinSubgroup n F N).subgroupOf (brauerInertia N iota phi)

instance spinInInertia_normal (phi : IBr iota) : (spinInInertia N iota phi).Normal := by
  change ((SpinSubgroup n F N).subgroupOf (brauerInertia N iota phi)).Normal
  infer_instance

/-- This is the canonical subgroup equivalence, not an arbitrary source
isomorphism of two groups called Spin. -/
def spinBaseEquiv (phi : IBr iota) : Spin n F N ≃* spinInInertia N iota phi :=
  (Subgroup.subgroupOfEquivOfLe (spin_le_brauerInertia N iota phi)).symm

/-- The base root is transported from the prescribed Spin root. -/
def inertiaBaseRoot (phi : IBr iota) := iota.alongMulEquiv (spinBaseEquiv N iota phi)

def inertiaBaseBrauer (phi : IBr iota) : IBr (inertiaBaseRoot N iota phi) :=
  IrreducibleBrauerCharacter.alongMulEquiv iota (spinBaseEquiv N iota phi) phi

/-- Membership in the actual inertia gives invariance in its embedded
Spin copy. All root and conjugation transports are canonical. -/
theorem inertiaBaseBrauer_fixed (phi : IBr iota)
    (a : brauerInertia N iota phi) :
    IrreducibleBrauerCharacter.twist (inertiaBaseRoot N iota phi)
      (inertiaBaseBrauer N iota phi) (MulAut.conjNormal a) =
        inertiaBaseBrauer N iota phi := by
  have hfix := (mem_brauerInertia N iota phi (a.1)⁻¹).mp
    ((brauerInertia N iota phi).inv_mem a.2)
  simp only [inv_inv] at hfix
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  have hvalue := congrArg (fun psi : IBr iota => psi.1
    (PrimeRegularElement.map (spinBaseEquiv N iota phi).symm.toMonoidHom x)) hfix
  exact hvalue

/-- Every literal Spin Brauer character extends to its ACTUAL special
Clifford inertia. This is an application of the source theorem after the
normal-subgroup, cyclic-quotient and invariance deductions, not an assumed
extension clause. The displayed representation affords the transported
character on precisely the embedded base. -/
theorem extends_to_specialClifford_inertia
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (quotient_cyclic : IsCyclic (SpecialClifford n F ⧸ SpinSubgroup n F N))
    (phi : IBr iota) :
    ∃ V : FDRep k (spinInInertia N iota phi),
      Representation.IsIrreducible V.ρ ∧
      (inertiaBaseBrauer N iota phi).1 =
        Representation.brauerCharacterOfRootEmbedding V.ρ (inertiaBaseRoot N iota phi) ∧
      Nonempty (Representation.Extension (spinInInertia N iota phi) V.ρ) := by
  let _ := quotient_cyclic
  exact Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
    principle (inertiaBaseRoot N iota phi) (inertiaBaseBrauer N iota phi)
    (subgroup_quotient_cyclic (SpinSubgroup n F N) (brauerInertia N iota phi))
    (inertiaBaseBrauer_fixed N iota phi)

variable [CharP F p] [NeZero f]
variable {parameters : OddFieldParameters F p f}

/-- Every literal Spin Brauer character extends to its stabilizer in
Spin semidirect the ACTUAL Frobenius group. This is stronger than the
criterion's clause for the conjugates of the selected constituents.
The embedded base, root, character, and conjugation square are constructed
by the checked cyclic-extension deduction. -/
theorem extends_to_spinField_inertia
    (S : FieldActionSource n F p f parameters N)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (psi : IBr iota) :
    let phi := spinFieldAction n F S
    let _ : MulAction (Spin n F N) (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : Spin n F N →* MulAut (Spin n F N))
    let _ : MulAction (FieldGroup f) (IBr iota) :=
      rightAutomorphismAction (X := IBr iota) phi
    let hcompat := rightAutomorphismSemidirectCompatible (X := IBr iota) phi
    let _ : MulAction (Spin n F N ⋊[phi] FieldGroup f) (IBr iota) :=
      semidirectMulAction phi hcompat
    let hinner : ∀ d : Spin n F N,
        (SemidirectProduct.inl d : Spin n F N ⋊[phi] FieldGroup f) • psi = psi :=
      fun d ↦ by
        rw [semidirect_inl_smul]
        exact inner_fixes_ibr iota d psi
    let eD := canonicalHToEmbeddedEquiv psi hinner
    let iotaEmbedded := iota.alongMulEquiv eD
    let psiEmbedded := IrreducibleBrauerCharacter.alongMulEquiv iota eD psi
    ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
      Representation.IsIrreducible W.ρ ∧
      psiEmbedded.1 =
        Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
      Nonempty (Representation.Extension (embeddedHStabilizer (phi := phi) psi) W.ρ) := by
  exact OddGFactorizationLemma312ActualExtension.lemma_3_12_cyclic_extension_actual
    iota (spinFieldAction n F S) principle psi

end ModularRep.PaperProofs.TypeBCyclicExtensionSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
