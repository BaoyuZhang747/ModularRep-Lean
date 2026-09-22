import ModularRep.PaperProofs.OddTwoLiteralSpathTarget
import ModularRep.PaperProofs.TypeCActualFrattiniFromWeightOrbit

/-!
# Own-pair ambient coordinates from the literal original odd-two target

Start with the actual `Definition41` data, not a `BlockWitness` to be
constructed. At every original radical Q the already computed local map
gives an own raw weight whose entire class is the global image. The SAME
matched ambient group fixes the canonical quotient Brauer character.
Transport through the canonical centreless quotient fixes the original
character and hence this corresponding weight class. The existing group theorem now
derives the Frattini equality for the actual embedded Q.

All constructions are K. There is no new source, root, character, subgroup
match, or target premise. The original matched local reductions, extensions,
intermediate block data, and BOTH Q=1 normalizations stay in the unchanged
input. This file does not construct a generic complete family witness or
claim the remaining character/block/normalization transports completed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalOwnPairAmbient

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.OddTwoLiteralSpathTarget
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

section AmbientCoordinates

variable (P : Problem n F) (psi : IBr P.iota)

/-- The original group to its OWN canonical central character quotient. -/
def quotientEquiv : X n F ≃*
    CentralCharacterQuotient (P.blockProblem (P.brauerBlock psi)) (P.ownBrauer psi) :=
  (centerlessCentralCharacterQuotientEquiv
    (P.blockProblem (P.brauerBlock psi)) P.center_eq_bot (P.ownBrauer psi)).symm

/-- This is the canonical quotient homomorphism, not a freely chosen map. -/
theorem quotientEquiv_apply (x : X n F) :
    quotientEquiv P psi x =
      centralCharacterQuotientMap (P.blockProblem (P.brauerBlock psi))
        (P.ownBrauer psi) x := by
  apply (centerlessCentralCharacterQuotientEquiv
    (P.blockProblem (P.brauerBlock psi)) P.center_eq_bot (P.ownBrauer psi)).injective
  exact ((centerlessCentralCharacterQuotientEquiv
    (P.blockProblem (P.brauerBlock psi)) P.center_eq_bot
      (P.ownBrauer psi)).apply_symm_apply x).trans
        (centerlessCentralCharacterQuotientEquiv_mk
          (P.blockProblem (P.brauerBlock psi)) P.center_eq_bot
            (P.ownBrauer psi) x).symm

variable (ambient : P.Ambient psi)

/-- Original X and the SAME stored ambient base. -/
def originalBaseEquiv : X n F ≃* ambient.base :=
  (quotientEquiv P psi).trans ambient.baseEquiv

/-- The displayed base map agrees with the target's named embedding. -/
theorem originalBaseEquiv_square :
    ambient.base.subtype.comp (originalBaseEquiv P psi ambient).toMonoidHom =
      P.baseEmbedding ambient := by
  apply MonoidHom.ext
  intro x
  change (ambient.baseEquiv (quotientEquiv P psi x) : ambient.A) =
    (ambient.baseEquiv
      (centralCharacterQuotientMap (P.blockProblem (P.brauerBlock psi))
        (P.ownBrauer psi) x) : ambient.A)
  rw [quotientEquiv_apply]

/-- The stored quotient conjugation, expressed on original X. -/
def originalAction : ambient.A →* MulAut (X n F) :=
  (MulAut.congr (quotientEquiv P psi).symm).toMonoidHom.comp ambient.conjugation

theorem quotientAction_square (a : ambient.A) (x : X n F) :
    quotientEquiv P psi (originalAction P psi ambient a x) =
      ambient.conjugation a (quotientEquiv P psi x) := by
  change quotientEquiv P psi ((quotientEquiv P psi).symm
    (ambient.conjugation a (quotientEquiv P psi x))) = _
  exact (quotientEquiv P psi).apply_symm_apply _

/-- Literal conjugation in the ambient group along the actual base inclusion. -/
theorem originalAction_on_base (a : ambient.A) (x : X n F) :
    TypeCActualFrattiniFromWeightOrbit.baseEmbedding ambient.base
        (originalBaseEquiv P psi ambient) (originalAction P psi ambient a x) =
      a * TypeCActualFrattiniFromWeightOrbit.baseEmbedding ambient.base
        (originalBaseEquiv P psi ambient) x * a⁻¹ := by
  change (ambient.baseEquiv
    (quotientEquiv P psi (originalAction P psi ambient a x)) : ambient.A) =
      a * (ambient.baseEquiv (quotientEquiv P psi x) : ambient.A) * a⁻¹
  rw [quotientAction_square]
  exact ambient.conjugation_on_base a (quotientEquiv P psi x)

/-- The actual automorphism-stabilizer coordinate fixes the OWN quotient
Brauer character. It makes no choice of an invariant raw representative. -/
theorem quotientBrauer_fixed (a : ambient.A) :
    inverseOpHom ambient.conjugation a • (P.quotientSource psi).brauer =
      (P.quotientSource psi).brauer := by
  have hf := (ambient.automorphismQuotientEquiv
    (QuotientGroup.mk' (Subgroup.center ambient.A) a)).2
  change ((ambient.automorphismQuotientEquiv
    (QuotientGroup.mk' (Subgroup.center ambient.A) a)) :
      (MulAut (CentralCharacterQuotient
        (P.blockProblem (P.brauerBlock psi)) (P.ownBrauer psi)))ᵐᵒᵖ) •
        (P.quotientSource psi).brauer = (P.quotientSource psi).brauer at hf
  rw [ambient.automorphismQuotientEquiv_natural] at hf
  exact hf

/-- Canonical quotient inflation on actual prime regular elements. The
stored root and character are used verbatim; no independent roots are equated. -/
theorem quotientBrauer_value (x : PrimeRegularElement (G := X n F) 2) :
    (P.quotientSource psi).brauer.1
      (PrimeRegularElement.map (quotientEquiv P psi).toMonoidHom x) = psi.1 x := by
  have h := congrArg
    (fun f : PrimeRegularClassFunction P.K (X n F) 2 => f x)
      (P.quotientSource psi).inflation
  change (P.quotientSource psi).brauer.1
    (PrimeRegularElement.map
      (centralCharacterQuotientMap (P.blockProblem (P.brauerBlock psi))
        (P.ownBrauer psi)) x) = psi.1 x at h
  have hm : PrimeRegularElement.map (quotientEquiv P psi).toMonoidHom x =
      PrimeRegularElement.map
        (centralCharacterQuotientMap (P.blockProblem (P.brauerBlock psi))
          (P.ownBrauer psi)) x := by
    apply Subtype.ext
    exact quotientEquiv_apply P psi x.1
  exact (congrArg
    (fun z : PrimeRegularElement (G := CentralCharacterQuotient
      (P.blockProblem (P.brauerBlock psi)) (P.ownBrauer psi)) 2 =>
        (P.quotientSource psi).brauer.1 z) hm).trans h

/-- Pullback of actual fixation through the canonical quotient square.
Only exact class-function equations are used, with the existing roots. -/
theorem originalBrauer_fixed (a : ambient.A) :
    inverseOpHom (originalAction P psi ambient) a • psi = psi := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  change psi.1 (PrimeRegularElement.map
    (originalAction P psi ambient a⁻¹).toMonoidHom x) = psi.1 x
  have hf := congrArg
    (fun chi : IBr (P.quotientSource psi).iota => chi.1
      (PrimeRegularElement.map (quotientEquiv P psi).toMonoidHom x))
        (quotientBrauer_fixed P psi ambient a)
  change (P.quotientSource psi).brauer.1
      (PrimeRegularElement.map (ambient.conjugation a⁻¹).toMonoidHom
        (PrimeRegularElement.map (quotientEquiv P psi).toMonoidHom x)) =
    (P.quotientSource psi).brauer.1
      (PrimeRegularElement.map (quotientEquiv P psi).toMonoidHom x) at hf
  have hm : PrimeRegularElement.map (quotientEquiv P psi).toMonoidHom
      (PrimeRegularElement.map (originalAction P psi ambient a⁻¹).toMonoidHom x) =
      PrimeRegularElement.map (ambient.conjugation a⁻¹).toMonoidHom
        (PrimeRegularElement.map (quotientEquiv P psi).toMonoidHom x) := by
    apply Subtype.ext
    exact quotientAction_square P psi ambient a⁻¹ x.1
  exact (quotientBrauer_value P psi
    (PrimeRegularElement.map (originalAction P psi ambient a⁻¹).toMonoidHom x)).symm.trans
      ((congrArg
        (fun z : PrimeRegularElement (G := CentralCharacterQuotient
          (P.blockProblem (P.brauerBlock psi)) (P.ownBrauer psi)) 2 =>
            (P.quotientSource psi).brauer.1 z) hm).trans
        (hf.trans (quotientBrauer_value P psi x)))

end AmbientCoordinates

section OriginalMatching

variable {P : Problem n F} (D : Definition41 P)
variable (Q : RadicalSubgroup (p := 2) (G := X n F)) (psi : D.map.Part Q)

/-- The own pair at this actual source Q, with its actual local-map character. -/
def ownPair : CharacterWeight 2 P.K (X n F) :=
  characterWeightAt Nat.prime_two Q (D.map.localMap Q psi)

@[simp] theorem ownPair_subgroup : (ownPair D Q psi).subgroup = Q.1 := rfl

@[simp] theorem ownPair_localCharacter :
    (ownPair D Q psi).localCharacter = (D.map.localMap Q psi).1 := rfl

/-- Full pair-class binding, rather than a radical-class-only equality. -/
theorem ownPair_class : weightClass (ownPair D Q psi) = D.map.equiv psi.1 :=
  IntrinsicGlobalToRepresentativeMaps.localMap_class
    P.iota D.map.equiv Nat.prime_two Q psi

/-- Class fixation of the own pair in the SAME matched ambient group. -/
theorem ownPair_class_fixed (a : (D.matched Q psi).ambient.A) :
    rightTwistConjugacyClass
      (originalAction P psi.1 (D.matched Q psi).ambient a)⁻¹
        (weightClass (ownPair D Q psi)) = weightClass (ownPair D Q psi) := by
  have heq := D.map.equivariant
    (inverseOpHom (originalAction P psi.1 (D.matched Q psi).ambient) a) psi.1
  rw [originalBrauer_fixed] at heq
  change D.map.equiv psi.1 = rightTwistConjugacyClass
    (originalAction P psi.1 (D.matched Q psi).ambient a⁻¹)
      (D.map.equiv psi.1) at heq
  rw [map_inv] at heq
  rw [ownPair_class]
  exact heq.symm

/-- The generic own-pair radical image is exactly the target's named image. -/
theorem embeddedOwnRadical_eq :
    TypeCActualFrattiniFromWeightOrbit.embeddedRadical
      (D.matched Q psi).ambient.base
      (originalBaseEquiv P psi.1 (D.matched Q psi).ambient) (ownPair D Q psi) =
        P.ambientRadical (D.matched Q psi).ambient Q := by
  change Q.1.map ((D.matched Q psi).ambient.base.subtype.comp
    (originalBaseEquiv P psi.1 (D.matched Q psi).ambient).toMonoidHom) = _
  rw [originalBaseEquiv_square]
  rfl

/-- Direct original-target Frattini equality. No complete family witness
or additional weight-orbit/source assertion is consumed. -/
theorem matched_frattini :
    (D.matched Q psi).ambient.base ⊔
      P.LocalGroup (D.matched Q psi).ambient Q = ⊤ := by
  have h := TypeCActualFrattiniFromWeightOrbit.frattini_of_weightClass_fixed
    (D.matched Q psi).ambient.base
    (originalBaseEquiv P psi.1 (D.matched Q psi).ambient)
    (originalAction P psi.1 (D.matched Q psi).ambient)
    (originalAction_on_base P psi.1 (D.matched Q psi).ambient)
    (ownPair D Q psi) (ownPair_class_fixed D Q psi)
  rw [embeddedOwnRadical_eq] at h
  exact h

/-- Every original intermediate J is covered, now with its Frattini
premise derived. The existing matched extensions and reductions are unchanged. -/
theorem matched_intermediate_eq
    (J : Subgroup (D.matched Q psi).ambient.A)
    (hJ : (D.matched Q psi).ambient.base ≤ J) :
    J = (D.matched Q psi).ambient.base ⊔
      (J ⊓ P.LocalGroup (D.matched Q psi).ambient Q) :=
  TypeCIntermediateNormalizerComparison.intermediate_eq_join_inf
    (D.matched Q psi).ambient.base
    (P.LocalGroup (D.matched Q psi).ambient Q) J hJ (matched_frattini D Q psi)

end OriginalMatching

end ModularRep.PaperProofs.TypeCOddTwoOriginalOwnPairAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
