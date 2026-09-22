import ModularRep.PaperProofs.TypeBQ3PrincipalRadicalDecoding
import ModularRep.PaperProofs.TypeBQ3TripleCoverAutomorphisms

/-!
# Full automorphism covariance of the retained principal seed

The actual matrix automorphism realization promotes the same SO-equivariant
seed to covariance for every opposite automorphism of G3. The inverse SO
actor preserves the existing action convention. Both supported steps are
identified on their literal character and weight-class values, so the result
has exactly the generic interface used by principal radical decoding.

The seed, its SO covariance and the specified block source are retained.
No new correspondence or source statement is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionSeedCovariance

open ModularRep CharacterWeight
open TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia TypeBCentralKernelCarriers
open TypeBQ3PrincipalWeightInflation

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- The retained seed has the exact automorphism covariance required by
TypeBQ3PrincipalRadicalDecoding on the same literal G3 carrier. -/
theorem seed_equivariant
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
    (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
    (seed : OmegaBrauer (ZMod 3) root b ≃ OmegaWeight (ZMod 3) S b)
    (seedSO : letI : Fintype (LiteralPrimitiveBlock k (G (ZMod 3))) :=
        S.operations.ambientBlockData.fintypeBlock
      ∀ (h : H (ZMod 3)) (theta : OmegaBrauer (ZMod 3) root b),
      seed (brauerStep (ZMod 3) S literal root b hb h theta) =
        weightStep (ZMod 3) S literal b hb h (seed theta))
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource) :
    letI : Fintype (LiteralPrimitiveBlock k (G (ZMod 3))) :=
      S.operations.ambientBlockData.fintypeBlock
    ∀ (alpha : (MulAut (G (ZMod 3)))ᵐᵒᵖ) (phi : OmegaBrauer (ZMod 3) root b),
      seed (TypeBQ3PrincipalBrauerInflation.principalStep root
        (coverDecomposition S literal) b hb alpha phi) =
        coverWeightStep S literal b hb alpha (seed phi) := by
  letI : Fintype (LiteralPrimitiveBlock k (G (ZMod 3))) :=
    S.operations.ambientBlockData.fintypeBlock
  intro alpha phi
  obtain ⟨h, hh⟩ := automorphisms.realizes alpha.unop
  have actor : conjugationOp (G (ZMod 3)) (h⁻¹) = alpha := by
    apply MulOpposite.unop_injective
    change originalAction (G (ZMod 3)) ((h⁻¹)⁻¹) = alpha.unop
    simpa only [inv_inv] using hh
  have brauerStep_eq : brauerStep (ZMod 3) S literal root b hb (h⁻¹) phi =
      TypeBQ3PrincipalBrauerInflation.principalStep root
        (coverDecomposition S literal) b hb alpha phi := by
    apply Subtype.ext
    change conjugationOp (G (ZMod 3)) (h⁻¹) • phi.val = alpha • phi.val
    rw [actor]
  calc
    seed (TypeBQ3PrincipalBrauerInflation.principalStep root
        (coverDecomposition S literal) b hb alpha phi) =
        seed (brauerStep (ZMod 3) S literal root b hb (h⁻¹) phi) :=
      congrArg seed brauerStep_eq.symm
    _ = weightStep (ZMod 3) S literal b hb (h⁻¹) (seed phi) := seedSO (h⁻¹) phi
    _ = coverWeightStep S literal b hb alpha (seed phi) := by
      apply Subtype.ext
      change conjugationOp (G (ZMod 3)) (h⁻¹) • (seed phi).val = alpha • (seed phi).val
      rw [actor]

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionSeedCovariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
