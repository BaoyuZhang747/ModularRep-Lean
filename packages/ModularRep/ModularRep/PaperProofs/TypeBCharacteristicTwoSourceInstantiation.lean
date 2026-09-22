import ModularRep.PaperProofs.TypeBCharacteristicTwoCorrespondenceSource
import ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherSource
import ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherProduct
import ModularRep.PaperProofs.TypeBCharacteristicTwoLinearCharacters

/-!
# Source-instantiated characteristic-two Clifford stabilizers

This endpoint binds every relation in the existing Lemma 4.6 deduction to
literal restriction support, the actual induction sum, or the published
Gallagher multiplication formula. It chooses the Clifford correspondent
internally. Scalar finiteness and oddness, quotient-scalar invariance,
restriction and induction naturality, and tensor commutation are K proofs.

The actual extension to the full Gamma_theta is the manuscript hypothesis.
With Gamma/N abelian this stronger extension permits direct invariance of
the Gallagher product. The existing checked odd-square stabilizer deduction
is still reused. Consequently its effective exponent-two hypothesis is
retained, though redundant for this particular product-based instantiation.
The proof works for any specified preserving E; the manuscript's cyclic E
is a specialization. Neither E cyclicity nor a global action on IBr(H_theta)
is manufactured as a source condition.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoSourceInstantiation

open TypeBLemma47LeviApplication
open TypeBCharacteristicTwoCliffordKernel TypeBCharacteristicTwoCliffordApplication
open TypeBCharacteristicTwoConstituentSource TypeBCharacteristicTwoCorrespondenceSource
open TypeBCharacteristicTwoExtensionCarriers TypeBCharacteristicTwoGallagherSource
open TypeBCharacteristicTwoGallagherProduct TypeBCharacteristicTwoLinearCharacters
open ModularRep.ManuscriptVerification.CharacteristicTwoClifford

universe u

variable {Gamma E k K : Type u}
variable [Group Gamma] [Finite Gamma] [Group E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Current Lemma 4.6 on the actual semidirect stabilizer, conditional only
on the displayed narrowly sourced Clifford/Gallagher/tensor certificates
and the lemma's own literal hypotheses. No selected correspondent, abstract
relation, scalar oddness, or desired factorization is a source premise. -/
theorem characteristic_two_clifford_source_instantiated
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
    (productFormula : BrauerLinearTensorProductFormula iotaI)
    (field : E →* MulAut Gamma)
    (hHstable : ∀ e : E, ∀ g : Gamma, g ∈ H ↔ field e g ∈ H)
    (hNstable : ∀ e : E, ∀ g : Gamma, g ∈ N ↔ field e g ∈ N)
    (quotient_exponent_two :
      letI : (effectiveConjugationKernel H).Normal := effectiveConjugationKernel_normal H;
      ∀ q : EffectiveConjugationQuotient H, q ^ 2 = 1)
    (theta_factorization :
      letI := ambientBrauerAction N iotaN;
      letI := fieldBrauerAction N iotaN field hNstable;
      Formalisation.SemidirectStabilizerFactors field
        (field_ambient_semidirect_compatible N iotaN field hNstable) theta) :
    letI := ambientBrauerAction H iotaH;
    letI := fieldBrauerAction H iotaH field hHstable;
    Formalisation.SemidirectStabilizerFactors field
      (field_ambient_semidirect_compatible H iotaH field hHstable) psi := by
  letI : MulAction Gamma (IBr iotaH) := ambientBrauerAction H iotaH
  letI : MulAction Gamma (IBr iotaN) := ambientBrauerAction N iotaN
  letI : MulAction E (IBr iotaH) := fieldBrauerAction H iotaH field hHstable
  letI : MulAction E (IBr iotaN) := fieldBrauerAction N iotaN field hNstable
  obtain ⟨eta, heta⟩ := source89.exists_correspondent psi
    ((occurs_iff_occursAlong H N hNH iotaH iotaN psi theta).mp chosen)
  have product := source820 H N hNH iotaN theta iotaI iotaA
    source89.roots_N_I roots_N_A roots_I_A extension eta heta.1
  letI : Finite (BrauerGallagherTwists (k := k) H N iotaN theta) :=
    linearCharactersTrivialOn_finite (k := k)
      (baseSubgroupInBrauerInertia H N iotaN theta)
  have hOdd : CharacteristicTwoLinearBrauerTwistGroup
      (BrauerGallagherTwists (k := k) H N iotaN theta) :=
    linearCharactersTrivialOn_odd_card (k := k)
      (baseSubgroupInBrauerInertia H N iotaN theta)
  have factorization := leviSelectedCharacter_productStabilizerFactorization
    H N hNH iotaH iotaN field hHstable hNstable psi theta iotaI productFormula eta
    (constituentOrbit H N hNH iotaH iotaN source89.roots_N_H
      field hHstable hNstable source87 psi theta chosen)
    (toCorrespondence H N hNH iotaH iotaN theta iotaI
      field hHstable hNstable source89 psi eta heta)
    (gallagherLinearTwistOfProduct H N iotaN theta iotaA extension.character
      iotaI productFormula eta product)
    hOdd quotient_exponent_two theta_factorization
  change ∀ a : Gamma ⋊[field] E,
    (a.left • (a.right • psi) = psi ↔
      a.left • psi = psi ∧ a.right • psi = psi)
  intro a
  exact factorization a.left a.right

end ModularRep.PaperProofs.TypeBCharacteristicTwoSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
