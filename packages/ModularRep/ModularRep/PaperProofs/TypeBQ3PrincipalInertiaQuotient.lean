import ModularRep.PaperProofs.TypeBQ3TripleCoverAutomorphisms
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-!
# Quotients of actual principal-character inertias at q = 3

The existing SO realization and index two bound the literal outer quotient.
Conjugation factors through the actual SO/Omega quotient because its values
on Omega are the same embedded inner automorphisms. Every actual Brauer
stabilizer quotient therefore has order at most two and is cyclic. These
group deductions support the extension step for the fixed correspondence.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalInertiaQuotient

open ModularRep
open TypeBRankThreePrincipalCountBinding
open TypeBQ3TripleCoverCarrier TypeBQ3TripleCoverAutomorphisms
open TypeBCentralKernelCarriers TypeBCentralKernelInertia
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-- The actual SO action followed by the literal outer quotient. -/
def soOuter : H (ZMod 3) →* LiteralOuterQuotient G3 :=
  (QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G3)).range).comp
    (conjugationOp (G (ZMod 3)))

/-- The base acts by the same inner embedding used in the outer quotient. -/
theorem omega_le_soOuter_kernel : G (ZMod 3) ≤ soOuter.ker := by
  intro h hh
  change (QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G3)).range)
    (conjugationOp (G (ZMod 3)) h) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨(⟨h, hh⟩ : G3), ?_⟩
  change MulOpposite.op (MulAut.conj ((⟨h, hh⟩ : G3)⁻¹)) =
    MulOpposite.op (originalAction (G (ZMod 3)) h⁻¹)
  exact congrArg MulOpposite.op
    (conjugation_inner (G (ZMod 3)) ((⟨h, hh⟩ : G3)⁻¹)).symm

/-- The induced homomorphism on the actual index-two quotient. -/
def quotientToOuter : H (ZMod 3) ⧸ G (ZMod 3) →* LiteralOuterQuotient G3 :=
  QuotientGroup.lift (G (ZMod 3)) soOuter omega_le_soOuter_kernel

theorem quotientToOuter_surjective (automorphisms : MatrixAutomorphismSource) :
    Function.Surjective quotientToOuter := by
  apply QuotientGroup.lift_surjective_of_surjective
  intro beta
  obtain ⟨alpha, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (RepresentationWeight.innerInverseOpHom (G := G3)).range beta
  obtain ⟨h, hh⟩ := automorphisms.realizes alpha.unop
  refine ⟨h⁻¹, ?_⟩
  change (QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G3)).range)
    (MulOpposite.op (originalAction (G (ZMod 3)) ((h⁻¹)⁻¹))) =
      (QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G3)).range) alpha
  simp only [inv_inv, hh, MulOpposite.op_unop]

theorem outer_card_le_two (automorphisms : MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2) :
    Nat.card (LiteralOuterQuotient G3) ≤ 2 := by
  have hcard : Nat.card (H (ZMod 3) ⧸ G (ZMod 3)) = 2 := by
    simpa only [Subgroup.index_eq_card] using indexTwo
  exact (Nat.card_le_card_of_surjective quotientToOuter
    (quotientToOuter_surjective automorphisms)).trans_eq hcard

theorem outer_isCyclic (automorphisms : MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2) : IsCyclic (LiteralOuterQuotient G3) := by
  have hcard : Nat.card (H (ZMod 3) ⧸ G (ZMod 3)) = 2 := by
    simpa only [Subgroup.index_eq_card] using indexTwo
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclic (H (ZMod 3) ⧸ G (ZMod 3)) := isCyclic_of_prime_card hcard
  exact isCyclic_of_surjective quotientToOuter
    (quotientToOuter_surjective automorphisms)

variable {k K : Type} [Field k] [Field K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The literal quotient of the actual character stabilizer by its base. -/
theorem actual_quotient_card_le_two (automorphisms : MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (iota : PrimeRegularRootEmbedding 2 k K G3) (phi : IBr iota) :
    Nat.card (ActualAutAmbient iota phi ⧸ actualBase iota phi) ≤ 2 :=
  (actual_quotient_card_le_outer iota phi).trans
    (outer_card_le_two automorphisms indexTwo)

theorem actual_quotient_isCyclic (automorphisms : MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (iota : PrimeRegularRootEmbedding 2 k K G3) (phi : IBr iota) :
    IsCyclic (ActualAutAmbient iota phi ⧸ actualBase iota phi) := by
  letI : IsCyclic (LiteralOuterQuotient G3) := outer_isCyclic automorphisms indexTwo
  exact isCyclic_of_injective (actualOuterEmbedding iota phi)
    (actualOuterEmbedding_injective iota phi)

theorem center_eq_bot (source : MatrixExceptionalSource) :
    Subgroup.center G3 = ⊥ :=
  TypeBExceptionalCanonicalCover.center_eq_bot_of_nonabelian_simple
    source.simple source.nonabelian

end ModularRep.PaperProofs.TypeBQ3PrincipalInertiaQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
