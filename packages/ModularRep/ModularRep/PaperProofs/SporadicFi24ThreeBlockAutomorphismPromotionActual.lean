import ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

/-!
# Full automorphism promotion for the Fischer three-block equivalence

The cancellation module constructs a literal block-preserving equivalence and
proves equivariance for one selected outer involution.  This module contains
only the group-theoretic step that promotes that conclusion to the full
automorphism group when the outer quotient has order two.

The quotient map, the nontriviality of the selected outer element, and the
identification of its kernel action on the literal carriers are `E1/U` source
matches.  Lean derives full equivariance.  No character-triple, extension,
BAW, or iBAW conclusion is an input or output of this module.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual

open Formalisation.BlockCancellation
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
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
variable {R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-- The exact external boundary for the standard identification
`Aut(X)/Inn(X) ≅ C₂` on the two literal carriers.  The operational kernel
fixation fields avoid importing an unrelated model of the inner subgroup. -/
structure C2OuterActionSource
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) where
  outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2)
  selectedOuter_nontrivial : outerClass S.outer ≠ 1
  kernel_fixes_brauer : ∀ alpha,
    outerClass alpha = 1 → ∀ phi : IBr iota, alpha • phi = phi
  kernel_fixes_weight : ∀ alpha,
    outerClass alpha = 1 →
      ∀ weight : WeightClass (p := 3) (K := K) (X := X),
        alpha • weight = weight

/-- The symmetric group on two points has a unique nonidentity element. -/
private theorem finTwo_perm_eq_of_ne_one
    (p q : Equiv.Perm (Fin 2)) (hp : p ≠ 1) (hq : q ≠ 1) : p = q := by
  have hcard : Fintype.card {r : Equiv.Perm (Fin 2) // r ≠ 1} = 1 := by
    decide
  obtain ⟨r, hr⟩ := Fintype.card_eq_one_iff.mp hcard
  exact congrArg Subtype.val ((hr ⟨p, hp⟩).trans (hr ⟨q, hq⟩).symm)

/-- Equivariance for the selected outer involution and kernel invariance imply
equivariance under every automorphism. -/
theorem fullAutomorphism_equivariant
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Source : C2OuterActionSource iota S)
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (houter : Intertwines Omega
      (totalBrauerPerm iota S) (totalWeightPerm (K := K) S)) :
    ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi := by
  intro alpha phi
  by_cases hclass : Source.outerClass alpha = 1
  · calc
      Omega (alpha • phi) = Omega phi :=
        congrArg Omega (Source.kernel_fixes_brauer alpha hclass phi)
      _ = alpha • Omega phi :=
        (Source.kernel_fixes_weight alpha hclass (Omega phi)).symm
  · have hclasses :
        Source.outerClass alpha = Source.outerClass S.outer :=
      finTwo_perm_eq_of_ne_one _ _ hclass Source.selectedOuter_nontrivial
    let innerPart : (MulAut X)ᵐᵒᵖ := alpha * S.outer⁻¹
    have hinnerClass : Source.outerClass innerPart = 1 := by
      simp only [innerPart, map_mul, map_inv, hclasses]
      exact mul_inv_cancel _
    have halpha : alpha = innerPart * S.outer := by
      simp [innerPart]
    have hselected : Omega (S.outer • phi) = S.outer • Omega phi := by
      simpa [totalBrauerPerm, totalWeightPerm] using houter phi
    calc
      Omega (alpha • phi) = Omega (innerPart • (S.outer • phi)) := by
        rw [halpha, mul_smul]
      _ = Omega (S.outer • phi) :=
        congrArg Omega
          (Source.kernel_fixes_brauer innerPart hinnerClass
            (S.outer • phi))
      _ = S.outer • Omega phi := hselected
      _ = innerPart • (S.outer • Omega phi) :=
        (Source.kernel_fixes_weight innerPart hinnerClass
          (S.outer • Omega phi)).symm
      _ = alpha • Omega phi := by rw [← mul_smul, ← halpha]

/-- The combined three-block equivalence is fully automorphism equivariant,
preserves literal blocks, and retains its two independently known fibre maps. -/
theorem exists_threeBlockAutEquivariantEquiv
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (Source : C2OuterActionSource iota S) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) =
          brauerBlock iota hinj blocks phi) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.nonprincipalBlock,
        Omega phi.1 = (Known.nonprincipal phi).1) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.defectZeroBlock,
        Omega phi.1 = (Known.defectZero phi).1) := by
  obtain ⟨Omega, houter, hblock, hnonprincipal, hdefectZero⟩ :=
    exists_threeBlockBlockwiseEquiv iota hinj blocks E1 F S Known
  exact ⟨Omega,
    fullAutomorphism_equivariant iota S Source Omega houter,
    hblock, hnonprincipal, hdefectZero⟩

end ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
