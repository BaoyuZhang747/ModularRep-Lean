import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerBinding
import ModularRep.PaperProofs.TypeBQ3PrincipalWeightBinding
import ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitBinding

/-!
# The principal SO correspondence for Omega(7,3)

The literal Brauer realization and specified weight covering determine the
two involution signatures. Finite C2 classification constructs a matching
on the complete principal fibres, and the actual index-two inclusion
promotes that same matching to every SO conjugation actor.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalOrbitApplication

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  [HasEnoughRootsOfUnity K (Nat.card (H (ZMod 3)))]
  (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
  (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
  (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
  (outside : delta ∉ G (ZMod 3))
  (SH : SOWeightSource (k := k) (K := K) (ZMod 3))
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (bH : LiteralPrimitiveBlock k (H (ZMod 3))) (hbH : IsPrincipal bH)
  [Fintype (OmegaBrauer (ZMod 3) root b)]
  [DecidableEq (OmegaBrauer (ZMod 3) root b)]
  [Fintype (OmegaWeight (ZMod 3) S b)]
  [DecidableEq (OmegaWeight (ZMod 3) S b)]
  [Fintype (SOWeight (ZMod 3) SH bH)]
  [DecidableEq (SOWeight (ZMod 3) SH bH)]
  (Msys : ModularSystem 2 K O k)
  (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G (ZMod 3)) Msys)
  (brauerSource : TypeBQ3PrincipalBrauerBinding.LiteralSource
    S literal root b hb delta indexTwo outside)
  (covering : TypeBQ3PrincipalWeightBinding.PublishedWeightCovering
    S literal b hb delta indexTwo outside SH literalH bH hbH Msys dgn)

include brauerSource covering in
/-- The principal C2-set correspondence and its SO promotion use the same
constructed equivalence of the complete specified fibres. -/
theorem exists_principalOmega_SO_equivariantEquiv :
    ∃ equivalence : OmegaBrauer (ZMod 3) root b ≃ OmegaWeight (ZMod 3) S b,
      (∀ theta,
        equivalence
            (brauerPermutation (ZMod 3) S literal root b hb delta indexTwo theta) =
          weightPermutation (ZMod 3) S literal b hb delta indexTwo
            (equivalence theta)) ∧
      (∀ (h : H (ZMod 3)) (theta : OmegaBrauer (ZMod 3) root b),
        equivalence (brauerStep (ZMod 3) S literal root b hb h theta) =
          weightStep (ZMod 3) S literal b hb h (equivalence theta)) := by
  have brauer := TypeBQ3PrincipalBrauerBinding.principalBrauer_action_signature
    S literal root b hb delta indexTwo outside brauerSource
  have weight := TypeBQ3PrincipalWeightBinding.principalWeight_action_signature
    S literal b hb delta indexTwo outside SH literalH bH hbH Msys dgn covering
  obtain ⟨equivalence, delta_equivariant⟩ :=
    Formalisation.C2Cancellation.exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
      (brauerPermutation (ZMod 3) S literal root b hb delta indexTwo)
      (weightPermutation (ZMod 3) S literal b hb delta indexTwo)
      (brauerStep_involutive (ZMod 3) S literal root b hb delta indexTwo)
      (weightStep_involutive (ZMod 3) S literal b hb delta indexTwo)
      ((congrArg Prod.fst brauer).trans (congrArg Prod.fst weight).symm)
      ((congrArg Prod.snd brauer).trans (congrArg Prod.snd weight).symm)
  refine ⟨equivalence, delta_equivariant, ?_⟩
  intro h theta
  exact TypeBRankThreePrincipalOrbitBinding.seed_H_equivariant
    (ZMod 3) S literal root b hb delta indexTwo outside
    equivalence delta_equivariant h theta

end ModularRep.PaperProofs.TypeBQ3PrincipalOrbitApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
