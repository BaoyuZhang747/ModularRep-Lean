import ModularRep.PaperProofs.SporadicFi24C2OuterActionFromBrauerWitness
import ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources

/-!
# The Fischer outer action from the nonprincipal Brauer census

The nonprincipal Brauer fibre has four elements, exactly two of which are
fixed by the selected outer involution.  This file deduces that the involution
moves a literal irreducible Brauer character and supplies that witness to the
existing cardinality two outer quotient construction.

The resulting construction still requires the order two outer quotient as a
source fact.  The moved character is proved from the restriction computation;
it is not an additional input.  No character to weight equivalence, principal
block statement, BAW condition, or iBAW condition is assumed here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24C2OuterActionFromNonprincipalCensus

open scoped MonoidAlgebra

open Formalisation.BlockCancellation
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24C2OuterActionFromBrauerWitness
open ModularRep.PaperProofs.SporadicFi24C2OuterQuotientCardTwoReduction
open ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- If the literal nonprincipal Brauer fibre has four elements but only two
fixed points, then the selected outer automorphism moves a literal Brauer
character. -/
theorem exists_brauer_moved_by_selectedOuter_of_nonprincipal_signature
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (hsignature :
      (Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock),
        Nat.card (Function.fixedPoints
          (nonprincipalBrauerPerm iota hinj blocks E1 S))) = (4, 2)) :
    ∃ phi : IBr iota, S.outer • phi ≠ phi := by
  let sigma := nonprincipalBrauerPerm iota hinj blocks E1 S
  have hmoved :
      ∃ phi : BrauerFibre iota hinj blocks S.nonprincipalBlock,
        sigma phi ≠ phi := by
    by_contra h
    push Not at h
    let fixedEquiv :
        BrauerFibre iota hinj blocks S.nonprincipalBlock ≃
          Function.fixedPoints sigma := {
      toFun phi := ⟨phi, h phi⟩
      invFun phi := phi.1
      left_inv _ := rfl
      right_inv phi := Subtype.ext rfl
    }
    have hcard := Nat.card_congr fixedEquiv
    have htotal :
        Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock) = 4 := by
      simpa using congrArg Prod.fst hsignature
    have hfixed :
        Nat.card (Function.fixedPoints sigma) = 2 := by
      simpa [sigma] using congrArg Prod.snd hsignature
    omega
  obtain ⟨phi, hphi⟩ := hmoved
  refine ⟨phi.1, ?_⟩
  intro hfixed
  apply hphi
  apply Subtype.ext
  simpa [sigma, nonprincipalBrauerPerm, brauerFibrePerm,
    Formalisation.stabilizerFibreEquiv_coe] using hfixed

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Package the order two outer quotient and the nonprincipal signature as the
existing literal Brauer witness source.  Moving a character is a deduction. -/
theorem brauerWitnessSource_of_nonprincipal_signature
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (hquotient :
      Nat.card
        ((MulAut X)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2)
    (hsignature :
      (Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock),
        Nat.card (Function.fixedPoints
          (nonprincipalBrauerPerm iota hinj blocks E1 S))) = (4, 2)) :
    Fi24C2OuterActionBrauerWitnessSource iota S where
  quotient_card_two := hquotient
  moves_brauer :=
    exists_brauer_moved_by_selectedOuter_of_nonprincipal_signature
      iota hinj blocks E1 S hsignature

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Construct the full selected outer action from the order two outer quotient
and the two computation alignments that imply the nonprincipal Brauer
signature. -/
noncomputable def c2OuterActionSource_of_nonprincipalBrauerComputation
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (hquotient :
      Nat.card
        ((MulAut X)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2)
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (A : Fi24P3NonprincipalBrauerComputationAlignment
      iota hinj blocks S D) :
    C2OuterActionSource iota S :=
  c2OuterActionSource_ofBrauerWitness iota S
    (brauerWitnessSource_of_nonprincipal_signature
      iota hinj blocks E1 S hquotient
      (nonprincipalBrauer_signature iota hinj blocks E1 S D A))

end ModularRep.PaperProofs.SporadicFi24C2OuterActionFromNonprincipalCensus


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
