import ModularRep.PaperProofs.TypeBQ3B2Application

/-!
The printed B2 Brauer-label action is bound to one actual nontrivial outer
actor. The exact inner kernel and the two-point quotient then determine the
action of every automorphism on the complete actual B2 Brauer fibre.

The matching helper consumes the weight count and fixedness already returned
by the B2 application. These are proof arguments to a construction, not fields
of a new source. The only new source field identifies the printed action on
the two B2 labels with the actual character action. It supplies no matching
or assertion quantified over the complete actual Brauer fibre.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2Matching

open Formalisation.ComputationArithmetic
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative
open ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalInnerRangeActual

variable {k K X : Type}
variable [Field k] [Field K] [CharZero K] [CharP k 2] [IsAlgClosed k]
variable [Group X] [Fintype X]
variable {blockIdempotent : Q3Block → k[X]}

/-- The computed permutation on B2's two labels, interpreted on the same
literal character map and chosen outer representative. -/
structure B2OuterBrauerActionSource
    (root : PrimeRegularRootEmbedding 2 k K X)
    (brauerMap : LiteralBrauerOutputMap root)
    (outer : (MulAut X)ᵐᵒᵖ) : Prop where
  action : ∀ label : BrauerOutputFibre .B2,
    outer • brauerMap.character label.val =
      brauerMap.character (brauerOuterAction label.val)

/-- The printed permutation fixes exactly the two labels in this fibre. -/
theorem printed_brauer_fixed : ∀ label : BrauerOutputFibre .B2,
    brauerOuterAction label.val = label.val := by
  decide

variable (blocks : BlockIdempotentDecomposition blockIdempotent)
  (root : PrimeRegularRootEmbedding 2 k K X)
  (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity root)
  (brauerMap : LiteralBrauerOutputMap root)
  (brauerMap_injective : Function.Injective brauerMap.character)
  (brauerMap_surjective : Function.Surjective brauerMap.character)
  (brauerBlock_compatible : BrauerBlockFibreCompatible root hinj blocks brauerMap)

include brauerMap_injective brauerMap_surjective brauerBlock_compatible in
/-- Completeness of the same table dictionary transports the printed
two-label calculation to every actual Brauer character in B2. -/
theorem outer_brauer_fixed
    (outer : (MulAut X)ᵐᵒᵖ)
    (source : B2OuterBrauerActionSource root brauerMap outer)
    (phi : ActualBrauerFibre root hinj blocks .B2) :
    outer • phi.val = phi.val := by
  obtain ⟨label, rfl⟩ :=
    (brauerBlockFibreEquiv root hinj blocks brauerMap brauerMap_injective
      brauerMap_surjective brauerBlock_compatible .B2).surjective phi
  change outer • brauerMap.character label.val = brauerMap.character label.val
  rw [source.action label, printed_brauer_fixed label]

include brauerMap_injective brauerMap_surjective brauerBlock_compatible in
/-- The exact two-point quotient and literal inner kernel upgrade the one
outer table action to fixation by every actual opposite automorphism. -/
theorem brauer_fixed
    (outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2))
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : outerClass outer ≠ 1)
    (outerClass_ker : outerClass.ker =
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (source : B2OuterBrauerActionSource root brauerMap outer)
    (alpha : (MulAut X)ᵐᵒᵖ)
    (phi : ActualBrauerFibre root hinj blocks .B2) :
    alpha • phi.val = phi.val := by
  by_cases hclass : outerClass alpha = 1
  · have hinner : alpha ∈ (RepresentationWeight.innerInverseOpHom (G := X)).range := by
      have hker : alpha ∈ outerClass.ker := hclass
      rwa [outerClass_ker] at hker
    exact innerInverseOpRange_fixes_brauer root alpha hinner phi.val
  · have hclasses : outerClass alpha = outerClass outer :=
      finTwo_perm_eq_of_ne_one _ _ hclass outer_nontrivial
    let innerPart : (MulAut X)ᵐᵒᵖ := alpha * outer⁻¹
    have hinnerClass : outerClass innerPart = 1 := by
      simp only [innerPart, map_mul, map_inv, hclasses]
      exact mul_inv_cancel _
    have hinner : innerPart ∈
        (RepresentationWeight.innerInverseOpHom (G := X)).range := by
      have hker : innerPart ∈ outerClass.ker := hinnerClass
      rwa [outerClass_ker] at hker
    have halpha : alpha = innerPart * outer := by simp [innerPart]
    calc
      alpha • phi.val = innerPart • (outer • phi.val) := by rw [halpha, mul_smul]
      _ = innerPart • phi.val := by
        rw [outer_brauer_fixed blocks root hinj brauerMap brauerMap_injective
          brauerMap_surjective brauerBlock_compatible outer source phi]
      _ = phi.val := innerInverseOpRange_fixes_brauer root innerPart hinner phi.val

include brauerMap_injective brauerMap_surjective brauerBlock_compatible in
/-- Fixation on the same restricted fibre action used by the routing API. -/
theorem brauer_fibre_fixed
    (outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2))
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : outerClass outer ≠ 1)
    (outerClass_ker : outerClass.ker =
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (source : B2OuterBrauerActionSource root brauerMap outer)
    (alpha : actualBlockStabilizer blocks .B2)
    (phi : ActualBrauerFibre root hinj blocks .B2) :
    brauerFibreAction root hinj blocks (canonical_brauerBlock_transport blocks root hinj)
      .B2 alpha phi = phi := by
  apply Subtype.ext
  exact brauer_fixed blocks root hinj brauerMap brauerMap_injective
    brauerMap_surjective brauerBlock_compatible outerClass outer outer_nontrivial
    outerClass_ker source alpha phi

include brauerMap_injective brauerMap_surjective brauerBlock_compatible in
/-- Construct the matching from the proved B2 weight conclusions and the
literal table dictionary. No independent finite carrier is supplied. -/
theorem exists_equivariant_matching_of_weight_card_and_fixed
    (outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2))
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : outerClass outer ≠ 1)
    (outerClass_ker : outerClass.ker =
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (source : B2OuterBrauerActionSource root brauerMap outer)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X) (Block := PrimitiveBlock k X))
    (weight_card : Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) = 2)
    (weight_fixed : ∀ (alpha : actualBlockStabilizer blocks .B2)
      (weight : R.Fibre (primitiveBlockOfLabel blocks .B2)), alpha • weight = weight) :
    ∃ matching : ActualBrauerFibre root hinj blocks .B2 ≃
        R.Fibre (primitiveBlockOfLabel blocks .B2),
      ∀ (alpha : actualBlockStabilizer blocks .B2)
        (phi : ActualBrauerFibre root hinj blocks .B2),
        matching (brauerFibreAction root hinj blocks
          (canonical_brauerBlock_transport blocks root hinj) .B2 alpha phi) =
            alpha • matching phi := by
  classical
  letI : Finite (R.Fibre (primitiveBlockOfLabel blocks .B2)) :=
    Nat.finite_of_card_ne_zero (by rw [weight_card]; decide)
  letI : Fintype (R.Fibre (primitiveBlockOfLabel blocks .B2)) := Fintype.ofFinite _
  have label_card : Fintype.card (BrauerOutputFibre .B2) =
      Fintype.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) := by
    calc
      Fintype.card (BrauerOutputFibre .B2) = 2 := brauerOutputFibre_card .B2
      _ = Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) := weight_card.symm
      _ = Fintype.card (R.Fibre (primitiveBlockOfLabel blocks .B2)) :=
        Nat.card_eq_fintype_card
  let labelWeight : BrauerOutputFibre .B2 ≃
      R.Fibre (primitiveBlockOfLabel blocks .B2) := Fintype.equivOfCardEq label_card
  let matching : ActualBrauerFibre root hinj blocks .B2 ≃
      R.Fibre (primitiveBlockOfLabel blocks .B2) :=
    (brauerBlockFibreEquiv root hinj blocks brauerMap brauerMap_injective
      brauerMap_surjective brauerBlock_compatible .B2).symm.trans labelWeight
  refine ⟨matching, ?_⟩
  intro alpha phi
  rw [brauer_fibre_fixed blocks root hinj brauerMap brauerMap_injective
    brauerMap_surjective brauerBlock_compatible outerClass outer outer_nontrivial
    outerClass_ker source alpha phi]
  exact (weight_fixed alpha (matching phi)).symm

end ModularRep.PaperProofs.TypeBQ3B2Matching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
