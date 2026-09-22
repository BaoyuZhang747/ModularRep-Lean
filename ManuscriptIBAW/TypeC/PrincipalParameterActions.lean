import ManuscriptIBAW.TypeC.PrincipalParameterCoordinates
import ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance

/-!
# Actions and counts on the principal parameters

The source action formulas concern the product subgroups and characters of
their normaliser quotients, indexed by the same staircase assignments. The
proof compares the resulting conjugacy classes, fixed point sets and
cardinalities. The counting source is stated on Feng–Malle's numerical
parameter set and supplies no weight bijection.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.OddTwoFYZPrincipalFullCarrierJoin
open ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance

universe u

variable {n : ℕ} {F k K Block Index : Type u}
variable [Field F] [Fintype F] [Field k] [CharP k 2] [IsAlgClosed k]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance parameterActionSpFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (fieldOdd : Odd (Nat.card F))
variable (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
variable (criterion : FYZPrincipalCriterion D)
variable (atlas : Index → PrincipalProductData (n := n) (F := F) (K := K))
variable (classification : PrincipalProductClassification atlas)
variable (lemma23 : FYZLemma23IntrinsicCertificate D)
variable (factors : PrincipalFactorSelection D)
variable (coordinates : FMProductCoordinates atlas)
variable (multiplicities : coordinates.MultiplicityClassification)

local instance parameterPrincipalWeightAction : MulAction (MulAut (Sp n F)) D.PrincipalWeight :=
  upstreamWeightAction D

local instance parameterPrincipalBrauerAction : MulAction (MulAut (Sp n F)) D.PrincipalBrauer :=
  upstreamBrauerAction D

/-- The constructed equivalence from the numerical parameter set to the
principal weight fibre. -/
def numericalPrincipalEquiv : FMParameter n ≃ D.PrincipalWeight :=
  (coordinates.parameterEquiv multiplicities).symm.trans
    (principalParameterEquiv D fieldOdd core criterion atlas classification lemma23 factors)

/-- The same pair used by the numerical equivalence, before passing to
conjugacy classes. Its ordinary character is the explicit wreath formula. -/
def numericalPair (h : FMParameter n) : CharacterWeight 2 K (Sp n F) :=
  let p := coordinates.decode multiplicities h
  (atlas p.1).pair fieldOdd core p.2

@[simp] theorem numericalPrincipalEquiv_val (h : FMParameter n) :
    (numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23 factors
      coordinates multiplicities h).1 =
      (Quotient.mk'' (Quotient.mk''
        (numericalPair fieldOdd core atlas coordinates multiplicities h)) :
          CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Sp n F)) := rfl

/-- The local action of FM Lemma 5.1 and the wreath calculation in the proof of
Proposition 5.5, expressed on the constructed product subgroups and actual
character functions. No equality of weight classes is a field. The inverse
on `a` follows the specified right action on characters. -/
structure FMParameterActionSource (a : MulAut (Sp n F))
    (sigma : FMParameter n → FMParameter n) where
  conjugator : FMParameter n → Sp n F
  subgroup_eq : ∀ h,
    (((numericalPair fieldOdd core atlas coordinates multiplicities h).rightTwist a⁻¹).rightTwist
      (MulAut.conj (conjugator h)⁻¹)).subgroup =
        (numericalPair fieldOdd core atlas coordinates multiplicities (sigma h)).subgroup
  character_eq : ∀ h,
    castLocalCharacter (subgroup_eq h)
      (((numericalPair fieldOdd core atlas coordinates multiplicities h).rightTwist a⁻¹).rightTwist
        (MulAut.conj (conjugator h)⁻¹)).localCharacter =
      (numericalPair fieldOdd core atlas coordinates multiplicities (sigma h)).localCharacter

variable {a : MulAut (Sp n F)} {sigma : FMParameter n → FMParameter n}
variable (action : FMParameterActionSource fieldOdd core atlas coordinates multiplicities a sigma)

theorem principalWeight_action_val (b : MulAut (Sp n F)) (w : D.PrincipalWeight) :
    (b • w).1 = rightTwistConjugacyClass b⁻¹ w.1 := rfl

include action in
theorem numericalPrincipalEquiv_action (h : FMParameter n) :
    numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23 factors
      coordinates multiplicities (sigma h) =
      a • numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23 factors
        coordinates multiplicities h := by
  apply Subtype.ext
  rw [numericalPrincipalEquiv_val, principalWeight_action_val,
    numericalPrincipalEquiv_val]
  change (Quotient.mk'' (Quotient.mk''
      (numericalPair fieldOdd core atlas coordinates multiplicities (sigma h))) :
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Sp n F)) =
    Quotient.mk'' (Quotient.mk''
      ((numericalPair fieldOdd core atlas coordinates multiplicities h).rightTwist a⁻¹))
  exact (weightClass_eq_of_conjugate_selectedPair (action.conjugator h)
    ⟨action.subgroup_eq h, action.character_eq h⟩).symm

def numericalPrincipalFixedEquiv :
    {h : FMParameter n // sigma h = h} ≃
      {w : D.PrincipalWeight // a • w = w} where
  toFun h := ⟨numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23
    factors coordinates multiplicities h.1, by
      rw [← numericalPrincipalEquiv_action D fieldOdd core criterion atlas classification
        lemma23 factors coordinates multiplicities action, h.2]⟩
  invFun w := ⟨(numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23
    factors coordinates multiplicities).symm w.1, by
      apply (numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23
        factors coordinates multiplicities).injective
      rw [numericalPrincipalEquiv_action D fieldOdd core criterion atlas classification lemma23
        factors coordinates multiplicities action, Equiv.apply_symm_apply, w.2]⟩
  left_inv h := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply _ h.1
  right_inv w := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply _ w.1

include action criterion classification lemma23 factors in
theorem numericalPrincipalFixed_card :
    Nat.card {w : D.PrincipalWeight // a • w = w} =
      Nat.card {h : FMParameter n // sigma h = h} :=
  Nat.card_congr (numericalPrincipalFixedEquiv D fieldOdd core criterion atlas classification
    lemma23 factors coordinates multiplicities action).symm

include fieldOdd core criterion classification lemma23 factors coordinates multiplicities in
theorem numericalPrincipal_card : Nat.card D.PrincipalWeight = Nat.card (FMParameter n) :=
  Nat.card_congr (numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23
    factors coordinates multiplicities).symm

include action criterion classification lemma23 factors in
theorem principalWeight_action_involutive (hsigma : Function.Involutive sigma) :
    Function.Involutive (fun w : D.PrincipalWeight => a • w) := by
  intro w
  obtain ⟨h, rfl⟩ := (numericalPrincipalEquiv D fieldOdd core criterion atlas classification
    lemma23 factors coordinates multiplicities).surjective w
  dsimp only
  rw [← numericalPrincipalEquiv_action D fieldOdd core criterion atlas classification lemma23
    factors coordinates multiplicities action,
    ← numericalPrincipalEquiv_action D fieldOdd core criterion atlas classification lemma23
      factors coordinates multiplicities action, hsigma]

include criterion classification lemma23 factors in
theorem principalWeight_fixed_of_trivial_parameter_action
    (fixedAction : FMParameterActionSource fieldOdd core atlas coordinates multiplicities a id)
    (w : D.PrincipalWeight) : a • w = w := by
  obtain ⟨h, rfl⟩ := (numericalPrincipalEquiv D fieldOdd core criterion atlas classification
    lemma23 factors coordinates multiplicities).surjective w
  exact (numericalPrincipalEquiv_action D fieldOdd core criterion atlas classification lemma23
    factors coordinates multiplicities fixedAction h).symm

/-- The combined numerical assumptions from Feng–Malle: the Brauer
parametrisation in Proposition 4.2 and Corollary 4.3, the identification of
colours and core towers in Proposition 5.4, the coefficient identity in the
proof of Proposition 6.1, and the fixed point count identity in the proof of
Theorem 6.2. They identify the counts of principal Brauer characters with
the numerical parameter counts. The weight count conclusion of Proposition
6.1 and a character–weight correspondence are not assumed. -/
structure FMPrincipalCountSource (diagonal : MulAut (Sp n F)) : Prop where
  rank_ge_two : 2 ≤ n
  odd_field : Odd (Nat.card F)
  total : Nat.card D.PrincipalBrauer = Nat.card (FMParameter n)
  diagonal_fixed : Nat.card {b : D.PrincipalBrauer // diagonal • b = b} =
    Nat.card {h : FMParameter n // fmParameterDiagonal n h = h}

include fieldOdd core criterion classification lemma23 factors coordinates multiplicities in
theorem principalWeight_finite : Finite D.PrincipalWeight :=
  Finite.of_equiv (FMParameter n)
    (numericalPrincipalEquiv D fieldOdd core criterion atlas classification lemma23 factors
      coordinates multiplicities)

variable (diagonal : MulAut (Sp n F)) (counts : FMPrincipalCountSource D diagonal)

include fieldOdd core criterion classification lemma23 factors coordinates multiplicities counts in
theorem principal_total_counts : Nat.card D.PrincipalBrauer = Nat.card D.PrincipalWeight :=
  counts.total.trans
    (numericalPrincipal_card D fieldOdd core criterion atlas classification lemma23 factors
      coordinates multiplicities).symm

include criterion classification lemma23 factors counts in
theorem principal_diagonal_fixed_counts
    (diagonalAction : FMParameterActionSource fieldOdd core atlas coordinates multiplicities
      diagonal (fmParameterDiagonal n)) :
    Nat.card {b : D.PrincipalBrauer // diagonal • b = b} =
      Nat.card {w : D.PrincipalWeight // diagonal • w = w} :=
  counts.diagonal_fixed.trans
    (numericalPrincipalFixed_card D fieldOdd core criterion atlas classification lemma23 factors
      coordinates multiplicities diagonalAction).symm

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
