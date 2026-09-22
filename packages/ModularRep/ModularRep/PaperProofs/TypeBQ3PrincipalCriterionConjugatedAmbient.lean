import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionRepresentatives

/-! Changing the base coordinates of the fixed actual automorphism ambient.
The ambient group, its base subgroup and all sets of characters stay fixed. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionConjugatedAmbient

open ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open TypeBQ3PrincipalCriterionRepresentatives

variable {p : Nat} {k K Y : Type}
variable [Field k] [Field K] [Group Y] [Finite Y]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (root : PrimeRegularRootEmbedding p k K Y) (phi : IBr root)

/-- The prescribed inner change of coordinates lands in the same base. -/
def baseEquiv (hc : Subgroup.center Y = ⊥) (x : Y) :
    Y ≃* actualBase root phi :=
  (MulAut.conj x).trans (actualBaseEquiv root phi hc)

theorem baseEquiv_apply (hc : Subgroup.center Y = ⊥) (x y : Y) :
    (baseEquiv root phi hc x y).val =
      conjugatedEmbedding (innerEmbedding root phi) x y := rfl

/-- The inverse inner change of coordinates on the same opposite inertia. -/
def ambientCoordinate (x : Y) : MulAut (ActualAutAmbient root phi) :=
  MulAut.conj ((innerEmbedding root phi x)⁻¹)

/-- The induced action for the conjugated base identification. -/
def adjustedConjugation (x : Y) : ActualAutAmbient root phi →* MulAut Y :=
  (actualConjugation root phi).comp (ambientCoordinate root phi x).toMonoidHom

theorem adjustedConjugation_apply (x : Y) (a : ActualAutAmbient root phi) :
    adjustedConjugation root phi x a =
      (MulAut.conj x)⁻¹ * actualConjugation root phi a * MulAut.conj x := by
  change actualConjugation root phi
      ((innerEmbedding root phi x)⁻¹ * a * ((innerEmbedding root phi x)⁻¹)⁻¹) = _
  rw [inv_inv, map_mul, map_mul, map_inv, actualConjugation_inner]

/-- Literal conjugation on the retained ambient agrees with the adjusted action. -/
theorem base_action (x y : Y) (a : ActualAutAmbient root phi) :
    conjugatedEmbedding (innerEmbedding root phi) x
        (adjustedConjugation root phi x a y) =
      a * conjugatedEmbedding (innerEmbedding root phi) x y * a⁻¹ := by
  rw [adjustedConjugation_apply]
  exact (conjugatedEmbedding_action_square
    (innerEmbedding root phi) x (MulAut.conj a) (actualConjugation root phi a)
    (fun z => (innerEmbedding_conjugation root phi a z).symm) y).symm

/-- The old central quotient is identified with the same full opposite inertia,
with the coordinate change required by the conjugated base. -/
def quotientEquiv (hc : Subgroup.center Y = ⊥) (x : Y) :
    ActualAutAmbient root phi ⧸ Subgroup.center (ActualAutAmbient root phi) ≃*
      ActualAutAmbient root phi :=
  (actualAutomorphismQuotientEquiv root phi hc).trans (ambientCoordinate root phi x)

theorem quotientEquiv_mk (hc : Subgroup.center Y = ⊥) (x : Y)
    (a : ActualAutAmbient root phi) :
    quotientEquiv root phi hc x
        (QuotientGroup.mk' (Subgroup.center (ActualAutAmbient root phi)) a) =
      ambientCoordinate root phi x a := by
  change ambientCoordinate root phi x
      (actualAutomorphismQuotientEquiv root phi hc
        (QuotientGroup.mk' (Subgroup.center (ActualAutAmbient root phi)) a)) = _
  rw [actualAutomorphismQuotientEquiv_mk]

/-- The quotient identification uses the exact opposite-action homomorphism. -/
theorem quotientEquiv_natural (hc : Subgroup.center Y = ⊥) (x : Y)
    (a : ActualAutAmbient root phi) :
    (quotientEquiv root phi hc x
      (QuotientGroup.mk' (Subgroup.center (ActualAutAmbient root phi)) a)).val =
        CyclicOuterLemma37Concrete.inverseOpHom (adjustedConjugation root phi x) a := by
  rw [quotientEquiv_mk]
  have natural := actualAutomorphismQuotientEquiv_natural root phi hc
    (ambientCoordinate root phi x a)
  rw [actualAutomorphismQuotientEquiv_mk] at natural
  exact natural

/-- The unchanged base has the required centralizer in the unchanged ambient. -/
theorem centralizer_eq_center (hc : Subgroup.center Y = ⊥) :
    Subgroup.centralizer (actualBase root phi : Set (ActualAutAmbient root phi)) =
      Subgroup.center (ActualAutAmbient root phi) := by
  rw [actualBase_centralizer_eq_bot root phi hc, actualAmbient_center_eq_bot root phi hc]

/-- The unchanged ambient centre has order prime to the characteristic. -/
theorem center_primeTo (hc : Subgroup.center Y = ⊥) :
    Nat.Coprime p (Nat.card (Subgroup.center (ActualAutAmbient root phi))) := by
  rw [actualAmbient_center_eq_bot root phi hc]
  simp

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionConjugatedAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
