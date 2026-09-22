import ModularRep.PaperProofs.TypeBCharacteristicTwoInduction
import ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource

/-!
# The literal Clifford correspondence in the characteristic-two window

The inducing subgroup is the actual H_theta and the base embedding is the
actual N -> H_theta map. Relatedness means precisely occurrence of theta
and the finite-sum Brauer induction equation. Navarro Theorem 8.9, p. 160,
supplies only existence and injectivity on this literal fibre, with root
agreement retained. It does not supply actions, equivariance, a stabilizer
factorization, or an arbitrary relation on characters.

The two local naturality laws are deductions from the original inclusion
squares, literal restriction-support reindexing and the checked induction
sum. Only Gamma_theta and E_theta act on the fixed inertia character group.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoCorrespondenceSource

open TypeBLemma47LeviApplication TypeBCharacteristicTwoCliffordKernel
open TypeBCharacteristicTwoCliffordApplication TypeBCharacteristicTwoInduction
open TypeBCharacteristicTwoConstituentSource
open ModularRep.ManuscriptVerification.CharacteristicTwoClifford

universe u

variable {Gamma E k K : Type u}
variable [Group Gamma] [Finite Gamma] [Group E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (H N : Subgroup Gamma) [H.Normal] [N.Normal] (hNH : N ≤ H)
variable (iotaH : PrimeRegularRootEmbedding 2 k K H)
variable (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)
variable (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))

local instance finiteEnumerationH : Fintype H := Fintype.ofFinite H

/-- The fixed literal Clifford relation. Neither constituent support nor
induction is represented by a free predicate. -/
def InductionRelated (psi : IBr iotaH) (eta : IBr iotaI) : Prop :=
  OccursAlong (baseEmbeddingInBrauerInertia H N hNH iotaN theta)
      iotaI iotaN eta theta ∧
    BrauerInduces (BrauerInertia H N iotaN theta) iotaI iotaH eta psi

/-- Narrow E1/U source: Navarro Theorem 8.9, p. 160, on the exact inertia
fibre. The root guards concern only actual subgroup-exponent roots, never
the zero-extended lift on the entire modular coefficient field. -/
structure Navarro89Source where
  roots_N_H : ∀ z : rootsOfUnity (primeRegularExponent 2 N) k,
    iotaN.lift (((z : kˣ) : k)) = iotaH.lift (((z : kˣ) : k))
  roots_I_H : ∀ z : rootsOfUnity
      (primeRegularExponent 2 (BrauerInertia H N iotaN theta)) k,
    iotaI.lift (((z : kˣ) : k)) = iotaH.lift (((z : kˣ) : k))
  roots_N_I : ∀ z : rootsOfUnity (primeRegularExponent 2 N) k,
    iotaN.lift (((z : kˣ) : k)) = iotaI.lift (((z : kˣ) : k))
  exists_correspondent : ∀ psi : IBr iotaH,
    OccursAlong (Subgroup.inclusion hNH) iotaH iotaN psi theta →
      ∃ eta : IBr iotaI, InductionRelated H N hNH iotaH iotaN theta iotaI psi eta
  injective_on_fibre : ∀ (psi : IBr iotaH) (eta eta' : IBr iotaI),
    InductionRelated H N hNH iotaH iotaN theta iotaI psi eta →
    InductionRelated H N hNH iotaH iotaN theta iotaI psi eta' → eta = eta'

local instance gammaNAction : MulAction Gamma (IBr iotaN) := ambientBrauerAction N iotaN
local instance gammaHAction : MulAction Gamma (IBr iotaH) := ambientBrauerAction H iotaH

local instance gammaInertiaAction :
    MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
  MulAction.compHom (IBr iotaI) (rightConjugationOnInertiaSubgroupHom H theta)

/-- Ambient inertia equivariance is derived on the actual subgroup maps. -/
theorem inductionRelated_gamma (a : MulAction.stabilizer Gamma theta)
    (psi : IBr iotaH) (eta : IBr iotaI)
    (h : InductionRelated H N hNH iotaH iotaN theta iotaI psi eta) :
    InductionRelated H N hNH iotaH iotaN theta iotaI ((a : Gamma) • psi) (a • eta) := by
  let alphaH : MulAut H := MulAut.conjNormal (H := H) (a : Gamma)⁻¹
  let alphaN : MulAut N := MulAut.conjNormal (H := N) (a : Gamma)⁻¹
  let alphaI : MulAut (BrauerInertia H N iotaN theta) :=
    conjugationOnInertia H theta (a : Gamma)⁻¹
      ((MulAction.stabilizer Gamma theta).inv_mem a.property)
  change InductionRelated H N hNH iotaH iotaN theta iotaI
    (IrreducibleBrauerCharacter.twist iotaH psi alphaH)
    (IrreducibleBrauerCharacter.twist iotaI eta alphaI)
  constructor
  · have square : ∀ x : N,
        alphaI (baseEmbeddingInBrauerInertia H N hNH iotaN theta x) =
          baseEmbeddingInBrauerInertia H N hNH iotaN theta (alphaN x) := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have ht := occursAlong_twist
      (baseEmbeddingInBrauerInertia H N hNH iotaN theta) iotaI iotaN
      alphaI alphaN square eta theta h.1
    have htheta : IrreducibleBrauerCharacter.twist iotaN theta alphaN = theta := a.property
    simpa only [htheta] using ht
  · exact BrauerInduces.twist_of_square (BrauerInertia H N iotaN theta) iotaI iotaH
      alphaH alphaI (fun _ ↦ rfl) h.2

variable (field : E →* MulAut Gamma)
variable (hHstable : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
variable (hNstable : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)

/-- Field inertia equivariance likewise uses the original pointwise field
action; the local character action is its constructed restriction. -/
theorem inductionRelated_field
    (e : @MulAction.stabilizer E (IBr iotaN) _
      (fieldBrauerAction N iotaN field hNstable) theta)
    (psi : IBr iotaH) (eta : IBr iotaI)
    (h : InductionRelated H N hNH iotaH iotaN theta iotaI psi eta) :
    letI := fieldBrauerAction N iotaN field hNstable;
    letI := fieldBrauerAction H iotaH field hHstable;
    letI := MulAction.compHom (IBr iotaI)
      (fieldRightActionOnInertiaSubgroupHom H theta field hHstable
        (field_ambient_brauer_naturality N iotaN field hNstable));
    InductionRelated H N hNH iotaH iotaN theta iotaI ((e : E) • psi) (e • eta) := by
  letI := fieldBrauerAction N iotaN field hNstable
  letI := fieldBrauerAction H iotaH field hHstable
  letI := MulAction.compHom (IBr iotaI)
    (fieldRightActionOnInertiaSubgroupHom H theta field hHstable
      (field_ambient_brauer_naturality N iotaN field hNstable))
  let alphaH : MulAut H := restrictAutomorphismHom H field hHstable (e : E)⁻¹
  let alphaN : MulAut N := restrictAutomorphismHom N field hNstable (e : E)⁻¹
  let alphaI : MulAut (BrauerInertia H N iotaN theta) :=
    fieldAutomorphismOnInertiaSubgroup H theta field hHstable
      (field_ambient_brauer_naturality N iotaN field hNstable) e⁻¹
  change InductionRelated H N hNH iotaH iotaN theta iotaI
    (IrreducibleBrauerCharacter.twist iotaH psi alphaH)
    (IrreducibleBrauerCharacter.twist iotaI eta alphaI)
  constructor
  · have square : ∀ x : N,
        alphaI (baseEmbeddingInBrauerInertia H N hNH iotaN theta x) =
          baseEmbeddingInBrauerInertia H N hNH iotaN theta (alphaN x) := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have ht := occursAlong_twist
      (baseEmbeddingInBrauerInertia H N hNH iotaN theta) iotaI iotaN
      alphaI alphaN square eta theta h.1
    have htheta : IrreducibleBrauerCharacter.twist iotaN theta alphaN = theta := e.property
    simpa only [htheta] using ht
  · exact BrauerInduces.twist_of_square (BrauerInertia H N iotaN theta) iotaI iotaH
      alphaH alphaI (fun _ ↦ rfl) h.2

/-- Construct the existing checked finite argument's correspondence packet
from the literal source. Both equivariance laws and unique induction target
are deductions; only source injectivity on the actual fibre is used. -/
def toCorrespondence (source : Navarro89Source H N hNH iotaH iotaN theta iotaI)
    (psi : IBr iotaH) (eta : IBr iotaI)
    (chosen : InductionRelated H N hNH iotaH iotaN theta iotaI psi eta) :
    letI := fieldBrauerAction N iotaN field hNstable;
    letI := fieldBrauerAction H iotaH field hHstable;
    letI := MulAction.compHom (IBr iotaI)
      (fieldRightActionOnInertiaSubgroupHom H theta field hHstable
        (field_ambient_brauer_naturality N iotaN field hNstable));
    StabilizerRestrictedCliffordCorrespondence (A := Gamma) (E := E) psi theta eta := by
  letI := fieldBrauerAction N iotaN field hNstable
  letI := fieldBrauerAction H iotaH field hHstable
  letI := MulAction.compHom (IBr iotaI)
    (fieldRightActionOnInertiaSubgroupHom H theta field hHstable
      (field_ambient_brauer_naturality N iotaN field hNstable))
  exact {
    Related := InductionRelated H N hNH iotaH iotaN theta iotaI
    chosen := chosen
    equivariant_A := fun a p u h ↦ inductionRelated_gamma H N hNH iotaH iotaN theta iotaI a p u h
    equivariant_E := fun e p u h ↦ inductionRelated_field H N hNH iotaH iotaN theta iotaI
      field hHstable hNstable e p u h
    unique_over_psi := fun u v hu hv ↦ source.injective_on_fibre psi u v hu hv
    unique_induced := fun p q u hp hq ↦
      BrauerInduces.unique (BrauerInertia H N iotaN theta) iotaI iotaH hp.2 hq.2 }

end ModularRep.PaperProofs.TypeBCharacteristicTwoCorrespondenceSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
