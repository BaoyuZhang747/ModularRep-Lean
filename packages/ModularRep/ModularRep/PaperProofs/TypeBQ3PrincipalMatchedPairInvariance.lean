import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding
import ModularRep.PaperProofs.TypeBQ3TripleCoverAutomorphisms

/-!
# Stabilizer invariance for the same principal matched pair

The actual matrix automorphism realization promotes the accepted principal
SO correspondence to invariance of each matched weight class. The inverse
SO actor gives the literal opposite action. The raw block support lemma
retains the original source and therefore permits its existing canonical
lower reduction to be used for the same ordinary character.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalMatchedPairInvariance

open ModularRep CharacterWeight
open TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelCarriers

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- Any raw representative of this matched class has the same principal block. -/
theorem matched_rawWeightBlock
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
    (b : LiteralPrimitiveBlock k (G (ZMod 3)))
    (seed : OmegaBrauer (ZMod 3) root b ≃ OmegaWeight (ZMod 3) S b)
    (phi : OmegaBrauer (ZMod 3) root b)
    (W : CharacterWeight 2 K (G (ZMod 3)))
    (matched : classOf W = (seed phi).val) :
    S.operations.rawWeightBlock W = b := by
  change S.weightBlock (classOf W) = b
  rw [matched]
  exact (seed phi).property

/-- A stabilizer of the actual principal character fixes its matched raw class. -/
theorem pairClassFixed
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
    (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
    (seed : OmegaBrauer (ZMod 3) root b ≃ OmegaWeight (ZMod 3) S b)
    (seedSO : ∀ (h : H (ZMod 3)) (theta : OmegaBrauer (ZMod 3) root b),
      seed (brauerStep (ZMod 3) S literal root b hb h theta) =
        weightStep (ZMod 3) S literal b hb h (seed theta))
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (phi : OmegaBrauer (ZMod 3) root b)
    (W : CharacterWeight 2 K (G (ZMod 3)))
    (matched : classOf W = (seed phi).val) :
    ∀ alpha : MulAut (G (ZMod 3)),
      MulOpposite.op alpha • phi.val = phi.val →
        MulOpposite.op alpha • classOf W = classOf W := by
  intro alpha fixed
  obtain ⟨h, hh⟩ := automorphisms.realizes alpha
  have actor : conjugationOp (G (ZMod 3)) (h⁻¹) = MulOpposite.op alpha := by
    apply MulOpposite.unop_injective
    change originalAction (G (ZMod 3)) ((h⁻¹)⁻¹) = alpha
    simpa only [inv_inv] using hh
  have fixedStep : brauerStep (ZMod 3) S literal root b hb (h⁻¹) phi = phi := by
    apply Subtype.ext
    change conjugationOp (G (ZMod 3)) (h⁻¹) • phi.val = phi.val
    rw [actor]
    exact fixed
  have step := congrArg Subtype.val (seedSO (h⁻¹) phi)
  change (seed (brauerStep (ZMod 3) S literal root b hb (h⁻¹) phi)).val =
    conjugationOp (G (ZMod 3)) (h⁻¹) • (seed phi).val at step
  rw [fixedStep, actor] at step
  rw [matched]
  exact step.symm

end ModularRep.PaperProofs.TypeBQ3PrincipalMatchedPairInvariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
