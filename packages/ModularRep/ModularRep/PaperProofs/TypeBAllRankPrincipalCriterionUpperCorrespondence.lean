import ModularRep.PaperProofs.TypeBGreenPrincipalConstituentSource
import ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource
import ModularRep.PaperProofs.TypeBPrincipalCommonTrivialTwist
import ModularRep.PaperProofs.TypeBPrincipalUpperPairBlockBinding
import ModularRep.PaperProofs.TypeBWeightCoveringSplittingSource
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionCarriers
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionFixedBlockSource
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum

/-!
# The actual upper principal correspondence from one/two cover fibres

The numerical inputs concern independent specified character and weight counts.
The upper equivalence is constructed by matching the double fibres and their
complements. Actual conjugation inertias, field covariance and quotient-linear
covariance are deductions. No downstairs matching is an input or output.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionUpperCorrespondence

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelCarriers TypeBCentralKernelPrincipalStability
open TypeBGreenPrincipalConstituentSource NavarroCoveringBrauerExtension
open TypeBRankThreePrincipalFieldNaturality
open scoped BigOperators Pointwise MonoidAlgebra Classical

local instance finiteFintype (X : Type) [Finite X] : Fintype X := Fintype.ofFinite X

section FiniteFibres

variable {X U V : Type} [Fintype X] [Fintype U] [Fintype V]

/-- Summing the literal one/two fibres gives the upper count plus its double stratum. -/
theorem card_eq_upper_add_double (q : X → U) (P : U → Prop)
    [DecidablePred P]
    (fibre : ∀ u, Fintype.card {x : X // q x = u} = if P u then 2 else 1) :
    Fintype.card X = Fintype.card U + Fintype.card {u : U // P u} := by
  classical
  calc
    Fintype.card X = ∑ u : U, Fintype.card {x : X // q x = u} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv q)).symm
    _ = ∑ u : U, (1 + if P u then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [fibre u]
      split_ifs <;> rfl
    _ = Fintype.card U + Fintype.card {u : U // P u} := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_one, Finset.sum_boole, Fintype.card_subtype, Nat.cast_id]

/-- The two independent stratum bijections combine into an upper equivalence. -/
def strataEquiv (P : U → Prop) (Q : V → Prop)
    [DecidablePred P] [DecidablePred Q]
    (total : Fintype.card U = Fintype.card V)
    (double : Fintype.card {u : U // P u} = Fintype.card {v : V // Q v}) : U ≃ V := by
  classical
  let yes : {u : U // P u} ≃ {v : V // Q v} := Fintype.equivOfCardEq double
  let no : {u : U // ¬ P u} ≃ {v : V // ¬ Q v} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, total, double])
  exact (Equiv.sumCompl P).symm.trans ((Equiv.sumCongr yes no).trans (Equiv.sumCompl Q))

theorem strataEquiv_double (P : U → Prop) (Q : V → Prop)
    [DecidablePred P] [DecidablePred Q]
    (total : Fintype.card U = Fintype.card V)
    (double : Fintype.card {u : U // P u} = Fintype.card {v : V // Q v}) (u : U) :
    Q (strataEquiv P Q total double u) ↔ P u := by
  classical
  by_cases hu : P u
  · have value : Q (strataEquiv P Q total double u) := by
      simpa only [strataEquiv, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_pos hu, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl] using
        (Fintype.equivOfCardEq double ⟨u, hu⟩).property
    exact iff_of_true value hu
  · have value : ¬ Q (strataEquiv P Q total double u) := by
      let e : {u : U // ¬ P u} ≃ {v : V // ¬ Q v} :=
        Fintype.equivOfCardEq (by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, total, double])
      simpa only [strataEquiv, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_neg hu, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr] using (e ⟨u, hu⟩).property
    exact iff_of_false value hu

end FiniteFibres

section IndexTwoOrbits

variable {H X U : Type} [Group H] [Finite H] [Fintype X]
  (G : Subgroup H) [G.Normal] (indexTwo : G.index = 2)
  (act : H →* Equiv.Perm X)
  (baseFixed : ∀ (h : H), h ∈ G → ∀ x, act h x = x)

include indexTwo in
theorem exists_outside : ∃ h : H, h ∉ G := by
  classical
  by_contra absent
  have all : ∀ h : H, h ∈ G := by
    intro h
    by_contra outside
    exact absent ⟨h, outside⟩
  have top : G = ⊤ := by
    ext h
    exact iff_of_true (all h) (Subgroup.mem_top h)
  have impossible : (1 : ℕ) = 2 := by simpa only [top, Subgroup.index_top] using indexTwo
  omega

include indexTwo baseFixed in
/-- Any outside actor represents the same nontrivial quotient coset. -/
theorem orbit_eq_or_step (d : H) (outside : d ∉ G) (x y : X) :
    (∃ h : H, act h x = y) ↔ y = x ∨ y = act d x := by
  constructor
  · rintro ⟨h, rfl⟩
    by_cases hh : h ∈ G
    · exact Or.inl (baseFixed h hh x)
    · right
      have base : h * d⁻¹ ∈ G := by
        apply (Subgroup.mul_mem_iff_of_index_two indexTwo).mpr
        simp only [Subgroup.inv_mem_iff, hh, outside]
      have factor : h = (h * d⁻¹) * d := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      rw [factor, map_mul]
      exact baseFixed (h * d⁻¹) base (act d x)
  · rintro (same | step)
    · exact ⟨1, by simpa only [map_one, Equiv.Perm.one_apply] using same.symm⟩
    · exact ⟨d, step.symm⟩

variable (q : X → U)
  (orbitFibre : ∀ x y : X, q x = q y ↔ ∃ h : H, act h x = y)

include indexTwo baseFixed orbitFibre in
theorem orbitFibre_card (d : H) (outside : d ∉ G) (x : X) :
    Fintype.card {y : X // q y = q x} = if act d x = x then 1 else 2 := by
  classical
  have pairCard : Fintype.card {y : X // q y = q x} =
      ({x, act d x} : Finset X).card := by
    apply Fintype.card_of_subtype
    intro y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ((orbitFibre x y).trans
      (orbit_eq_or_step G indexTwo act baseFixed d outside x y)).symm.trans eq_comm
  rw [pairCard]
  by_cases fixed : act d x = x
  · simp only [fixed, Finset.insert_eq_of_mem (Finset.mem_singleton_self x),
      Finset.card_singleton, if_true]
  · rw [if_neg fixed]
    exact Finset.card_pair_eq_two_iff.mpr (Ne.symm fixed)

include indexTwo baseFixed orbitFibre in
theorem orbitFibre_one_or_two (surjective : Function.Surjective q) (u : U) :
    Fintype.card {x : X // q x = u} = 1 ∨ Fintype.card {x : X // q x = u} = 2 := by
  obtain ⟨d, outside⟩ := exists_outside G indexTwo
  obtain ⟨x, rfl⟩ := surjective u
  rw [orbitFibre_card G indexTwo act baseFixed q orbitFibre d outside x]
  split_ifs <;> simp only [or_true, true_or]

include indexTwo baseFixed orbitFibre in
/-- An outside actor fixes a point exactly when its actual quotient fibre is singleton. -/
theorem outside_fixed_iff_fibre_one (h : H) (outside : h ∉ G) (x : X) :
    act h x = x ↔ Fintype.card {y : X // q y = q x} = 1 := by
  classical
  rw [orbitFibre_card G indexTwo act baseFixed q orbitFibre h outside x]
  by_cases fixed : act h x = x <;> simp [fixed]

end IndexTwoOrbits

section Matching

variable {A X Y U V : Type} [Group A] [Finite A]
  [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
  (G : Subgroup A) [G.Normal] (indexTwo : G.index = 2)
  (actX : A →* Equiv.Perm X) (actY : A →* Equiv.Perm Y)
  (fixedX : ∀ h : A, h ∈ G → ∀ x, actX h x = x)
  (fixedY : ∀ h : A, h ∈ G → ∀ y, actY h y = y)
  (q : X → U) (r : Y → V)
  (qOrbit : ∀ x x', q x = q x' ↔ ∃ h : A, actX h x = x')
  (rOrbit : ∀ y y', r y = r y' ↔ ∃ h : A, actY h y = y')
  (qOnto : Function.Surjective q) (rOnto : Function.Surjective r)

include indexTwo fixedX fixedY qOrbit rOrbit qOnto rOnto in
/-- Only upper counts, the lower character count and the weight double count
are used. Equality of lower character and weight totals is not an input. -/
theorem exists_matching_of_counts (u d : ℕ)
    (upperX : Fintype.card U = u) (upperY : Fintype.card V = u)
    (lowerX : Fintype.card X = u + d)
    (doubleY : Fintype.card {v : V // Fintype.card {y : Y // r y = v} = 2} = d) :
    ∃ E : U ≃ V, ∀ (x : X) (y : Y), r y = E (q x) →
      ∀ h : A, actX h x = x ↔ actY h y = y := by
  classical
  let P : U → Prop := fun v => Fintype.card {x : X // q x = v} = 2
  let Q : V → Prop := fun v => Fintype.card {y : Y // r y = v} = 2
  have qCard (v : U) : Fintype.card {x : X // q x = v} = if P v then 2 else 1 := by
    have cases := orbitFibre_one_or_two G indexTwo actX fixedX q qOrbit qOnto v
    dsimp only [P]
    split_ifs <;> omega
  have sumCard := card_eq_upper_add_double q P qCard
  have doubleX : Fintype.card {v : U // P v} = d := by
    rw [upperX, lowerX] at sumCard
    omega
  have total : Fintype.card U = Fintype.card V := upperX.trans upperY.symm
  have doubles : Fintype.card {v : U // P v} = Fintype.card {v : V // Q v} :=
    doubleX.trans doubleY.symm
  let E := strataEquiv P Q total doubles
  refine ⟨E, ?_⟩
  intro x y matched h
  by_cases base : h ∈ G
  · exact iff_of_true (fixedX h base x) (fixedY h base y)
  · rw [outside_fixed_iff_fibre_one G indexTwo actX fixedX q qOrbit h base x,
      outside_fixed_iff_fibre_one G indexTwo actY fixedY r rOrbit h base y]
    have two : Fintype.card {y' : Y // r y' = r y} = 2 ↔
        Fintype.card {x' : X // q x' = q x} = 2 := by
      rw [matched]
      exact strataEquiv_double P Q total doubles (q x)
    have cx := orbitFibre_one_or_two G indexTwo actX fixedX q qOrbit qOnto (q x)
    have cy := orbitFibre_one_or_two G indexTwo actY fixedY r rOrbit rOnto (r y)
    omega

end Matching

/-- The usual admissibility condition for odd orthogonal unipotent partitions. -/
def admissible {w : ℕ} (lambda : Nat.Partition w) : Prop :=
  ∀ i ∈ lambda.parts, Even i → Even (lambda.parts.count i)

def oddSupportCard {w : ℕ} (lambda : Nat.Partition w) : ℕ :=
  (lambda.parts.toFinset.filter Odd).card

/-- Even parts of even multiplicity remain allowed in this double stratum. -/
def oddMultiplicityOne {w : ℕ} (lambda : Nat.Partition w) : Prop :=
  ∀ i ∈ lambda.parts, Odd i → lambda.parts.count i = 1

def U (n : ℕ) : ℕ :=
  ∑ lambda ∈ Finset.univ.filter (admissible (w := 2 * n + 1)),
    2 ^ (oddSupportCard lambda - 1)

def D (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun lambda : Nat.Partition (2 * n + 1) =>
    admissible lambda ∧ oddMultiplicityOne lambda)).card

theorem U_pos (n : ℕ) : 0 < U n := by
  let lambda := Nat.Partition.indiscrete (2 * n + 1)
  have nonzero : 2 * n + 1 ≠ 0 := by omega
  have valid : admissible lambda := by
    intro i member even
    have equal : i = 2 * n + 1 := by
      simpa only [lambda, Nat.Partition.indiscrete_parts nonzero,
        Multiset.mem_singleton] using member
    subst i
    exact False.elim (Nat.not_even_two_mul_add_one n even)
  have member : lambda ∈ Finset.univ.filter (admissible (w := 2 * n + 1)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid⟩
  exact lt_of_lt_of_le (pow_pos (by decide : (0 : ℕ) < 2) _)
    (Finset.single_le_sum (f := fun lambda => 2 ^ (oddSupportCard lambda - 1))
      (fun _ _ => Nat.zero_le _) member)

local instance physicalSubgroupFintype {A : Type} [Group A] [Finite A]
    (G : Subgroup A) : Fintype G := Fintype.ofFinite G

section PhysicalConstituents

variable {k K A : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k]
  [CharZero K] [Group A] [Finite A]
  (G : Subgroup A) [G.Normal]
  (SX : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K) G)
  (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
  (rootX : PrimeRegularRootEmbedding 2 k K G)
  (bX : LiteralPrimitiveBlock k G) (principalX : IsPrincipal bX)

/-- The supported action has precisely the existing opposite-conjugation values. -/
def brauerAction : A →* Equiv.Perm (BrauerFibre rootX bX) := by
  letI := SX.operations.ambientBlockData.fintypeBlock
  letI := principalFibreMulAction (physicalDecomposition SX literalX) rootX bX principalX
  exact (MulAction.toPermHom (MulAut G)ᵐᵒᵖ (BrauerFibre rootX bX)).comp (conjugationOp G)

@[simp] theorem brauerAction_val (h : A) (theta : BrauerFibre rootX bX) :
    (brauerAction G SX literalX rootX bX principalX h theta).val =
      conjugationOp G h • theta.val := rfl

theorem brauerAction_base (h : A) (base : h ∈ G) (theta : BrauerFibre rootX bX) :
    brauerAction G SX literalX rootX bX principalX h theta = theta :=
  Subtype.ext (G_le_T G rootX theta.val base)

def weightAction : A →* Equiv.Perm (SX.Fibre bX) := by
  letI := principalWeightOpAction SX literalX bX principalX
  exact (MulAction.toPermHom (MulAut G)ᵐᵒᵖ (SX.Fibre bX)).comp (conjugationOp G)

@[simp] theorem weightAction_val (h : A) (w : SX.Fibre bX) :
    (weightAction G SX literalX bX principalX h w).val = conjugationOp G h • w.val := rfl

theorem inner_fixes_weightClass (g : G)
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G)) :
    conjugationOp G (g : A) • w = w := by
  refine Quotient.inductionOn w ?_
  intro W
  change (Quotient.mk'' (conjugationOp G (g : A) • W) :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G)) = Quotient.mk'' W
  rw [iso_action_inner]
  exact Quotient.sound ⟨g, rfl⟩

theorem weightAction_base (h : A) (base : h ∈ G) (w : SX.Fibre bX) :
    weightAction G SX literalX bX principalX h w = w :=
  Subtype.ext (inner_fixes_weightClass G ⟨h, base⟩ w.val)

variable (rootH : PrimeRegularRootEmbedding 2 k K A)
  (bH : LiteralPrimitiveBlock k A) (principalH : IsPrincipal bH)
  (roots : RootAgreement G rootH rootX)
  (coefficient : SpathCoefficientField 2 k rootH.prime)
  (indexTwo : G.index = 2)
  (green : Green811Source G rootH rootX roots coefficient (quotient_isTwoGroup G indexTwo))
  (principalLift : PrincipalLiftSource G rootH rootX roots coefficient
    (quotient_isTwoGroup G indexTwo))

/-- Green's unique character, supported in the same specified principal block. -/
def principalAbove (theta : BrauerFibre rootX bX) : BrauerFibre rootH bH :=
  ⟨above G rootH rootX roots coefficient (quotient_isTwoGroup G indexTwo) green theta.val,
    principalLift.lifts_principal bH bX principalH principalX _ theta.val theta.property
      (above_occurs G rootH rootX roots coefficient (quotient_isTwoGroup G indexTwo)
        green theta.val)⟩

local notation "up" => principalAbove G rootX bX principalX rootH bH principalH
  roots coefficient indexTwo green principalLift

theorem principalAbove_occurs (theta : BrauerFibre rootX bX) :
    BrauerOccursInRestriction G rootH rootX (up theta).val theta.val :=
  above_occurs G rootH rootX roots coefficient (quotient_isTwoGroup G indexTwo) green theta.val

theorem principalAbove_eq (theta : BrauerFibre rootX bX) (Phi : BrauerFibre rootH bH)
    (occurs : BrauerOccursInRestriction G rootH rootX Phi.val theta.val) : up theta = Phi :=
  Subtype.ext (above_eq G rootH rootX roots coefficient (quotient_isTwoGroup G indexTwo)
    green theta.val Phi.val occurs)

theorem principalAbove_step (h : A) (theta : BrauerFibre rootX bX) :
    up (brauerAction G SX literalX rootX bX principalX h theta) = up theta := by
  apply principalAbove_eq G rootX bX principalX rootH bH principalH roots coefficient
    indexTwo green principalLift
  have transported := TypeBCharacteristicTwoConstituentSource.occursInRestriction_twist
    G rootH rootX (MulAut.conj h⁻¹) (originalAction G h⁻¹) (fun _ => rfl)
    (up theta).val theta.val
    (principalAbove_occurs G rootX bX principalX rootH bH principalH roots coefficient
      indexTwo green principalLift theta)
  have fixed : IrreducibleBrauerCharacter.twist rootH (up theta).val (MulAut.conj h⁻¹) =
      (up theta).val := by
    apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    exact PrimeRegularClassFunction.twist_conj (up theta).val.val h⁻¹
  exact fixed ▸ transported

variable (clifford : Clifford85_87Source G rootH rootX roots coefficient)
  (principalRestriction : PrincipalRestrictionSource G rootH rootX roots coefficient)

include clifford in
theorem principalAbove_orbit (theta eta : BrauerFibre rootX bX) :
    up theta = up eta ↔
      ∃ h : A, brauerAction G SX literalX rootX bX principalX h theta = eta := by
  constructor
  · intro equal
    have occursEta := principalAbove_occurs G rootX bX principalX rootH bH principalH
      roots coefficient indexTwo green principalLift eta
    rw [← equal] at occursEta
    obtain ⟨h, values⟩ := clifford.constituents_conjugate (up theta).val theta.val eta.val
      (principalAbove_occurs G rootX bX principalX rootH bH principalH roots coefficient
        indexTwo green principalLift theta) occursEta
    exact ⟨h, Subtype.ext values⟩
  · rintro ⟨h, rfl⟩
    exact (principalAbove_step G SX literalX rootX bX principalX rootH bH principalH
      roots coefficient indexTwo green principalLift h theta).symm

include clifford principalRestriction in
theorem principalAbove_surjective : Function.Surjective up := by
  intro Phi
  obtain ⟨theta, occurs⟩ := clifford.constituent_exists Phi.val
  let constituent : BrauerFibre rootX bX :=
    ⟨theta, principalRestriction.restricts_principal bH bX principalH principalX
      Phi.val theta Phi.property occurs⟩
  exact ⟨constituent, principalAbove_eq G rootX bX principalX rootH bH principalH
    roots coefficient indexTwo green principalLift constituent Phi occurs⟩

include principalX principalH clifford principalRestriction principalLift in
theorem character_union (Phi : IBr rootH) :
    Supported rootH bH Phi ↔ ∃ theta : BrauerFibre rootX bX,
      BrauerOccursInRestriction G rootH rootX Phi theta.val := by
  constructor
  · intro supported
    obtain ⟨theta, occurs⟩ := clifford.constituent_exists Phi
    exact ⟨⟨theta, principalRestriction.restricts_principal bH bX principalH principalX
      Phi theta supported occurs⟩, occurs⟩
  · rintro ⟨theta, occurs⟩
    exact principalLift.lifts_principal bH bX principalH principalX Phi theta.val
      theta.property occurs

variable (SH : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K) A)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)

theorem principalAbove_natural (alphaH : MulAut A) (alphaX : MulAut G)
    (square : ∀ x : G, (alphaX x).val = alphaH x.val) (theta : BrauerFibre rootX bX) :
    up (brauerTwistEquiv SX literalX rootX bX principalX alphaX theta) =
      brauerTwistEquiv SH literalH rootH bH principalH alphaH (up theta) := by
  apply principalAbove_eq G rootX bX principalX rootH bH principalH roots coefficient
    indexTwo green principalLift
  exact TypeBCharacteristicTwoConstituentSource.occursInRestriction_twist G rootH rootX
    alphaH alphaX (fun x => (square x).symm) (up theta).val theta.val
    (principalAbove_occurs G rootX bX principalX rootH bH principalH roots coefficient
      indexTwo green principalLift theta)

include SX literalX principalX principalH green principalLift clifford principalRestriction
  SH literalH in
/-- Upper fixation is a consequence of lower fixation and actual restriction. -/
theorem upper_fixed_of_lower_fixed (alphaH : MulAut A) (alphaX : MulAut G)
    (square : ∀ x : G, (alphaX x).val = alphaH x.val)
    (fixed : ∀ theta : BrauerFibre rootX bX,
      IrreducibleBrauerCharacter.twist rootX theta.val alphaX = theta.val)
    (Phi : BrauerFibre rootH bH) :
    IrreducibleBrauerCharacter.twist rootH Phi.val alphaH = Phi.val := by
  obtain ⟨theta, rfl⟩ := principalAbove_surjective G rootX bX principalX rootH bH principalH
    roots coefficient indexTwo green principalLift clifford principalRestriction Phi
  have lower : brauerTwistEquiv SX literalX rootX bX principalX alphaX theta = theta :=
    Subtype.ext (fixed theta)
  have natural := principalAbove_natural G SX literalX rootX bX principalX rootH bH principalH
    roots coefficient indexTwo green principalLift SH literalH alphaH alphaX square theta
  rw [lower] at natural
  exact (congrArg Subtype.val natural).symm

end PhysicalConstituents

section PhysicalCovering

variable {k K O A : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k]
  [CharZero K] [CommRing O] [IsDomain O] [Algebra O K] [Group A] [Finite A]
  (G : Subgroup A) [G.Normal]
  (SX : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K) G)
  (bX : LiteralPrimitiveBlock k G)
  (SH : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K) A)
  (bH : LiteralPrimitiveBlock k A)
  (Msys : ModularSystem 2 K O k) [HasEnoughRootsOfUnity K (Nat.card A)]
  (dgn : TypeBWeightCoveringSplittingSource.DGNSource G Msys)

/-- One-way specified covering facts, on the original classes and calibrated
DGN relation. Uniqueness ranges over ALL upper classes, as in FYZ's statement;
the independently given principal cover therefore excludes nonprincipal covers.
These assert no matching, action covariance, or inertia equality. -/
structure PublishedPrincipalCovering : Prop where
  exists_above : ∀ w : SX.Fibre bX, ∃ v : SH.Fibre bH,
    TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w.val
  unique_above : ∀ (w : SX.Fibre bX)
      (v v' : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := A)),
    TypeBWeightCoveringSplittingSource.CoversClass G dgn v w.val →
    TypeBWeightCoveringSplittingSource.CoversClass G dgn v' w.val → v = v'
  nonempty_fibre : ∀ v : SH.Fibre bH, ∃ w : SX.Fibre bX,
    TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w.val
  covered_orbit : ∀ (v : SH.Fibre bH) (w w' : SX.Fibre bX),
    TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w.val →
    (TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w'.val ↔
      ∃ h : A, conjugationOp G h • w.val = w'.val)

variable {G SX bX SH bH Msys dgn}
  (covering : PublishedPrincipalCovering G SX bX SH bH Msys dgn)
  (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
  (principalX : IsPrincipal bX)

def weightAbove (w : SX.Fibre bX) : SH.Fibre bH :=
  Classical.choose (covering.exists_above w)

theorem weightAbove_covers (w : SX.Fibre bX) :
    TypeBWeightCoveringSplittingSource.CoversClass G dgn (weightAbove covering w).val w.val :=
  Classical.choose_spec (covering.exists_above w)

theorem weightAbove_eq_iff (v : SH.Fibre bH) (w : SX.Fibre bX) :
    weightAbove covering w = v ↔
      TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w.val := by
  constructor
  · intro same
    rw [← same]
    exact weightAbove_covers covering w
  · intro related
    exact Subtype.ext (covering.unique_above w (weightAbove covering w).val v.val
      (weightAbove_covers covering w) related)

include covering in
theorem principal_above
    (v : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := A)) (w : SX.Fibre bX)
    (related : TypeBWeightCoveringSplittingSource.CoversClass G dgn v w.val) :
    SH.weightBlock v = bH := by
  have equal := covering.unique_above w v (weightAbove covering w).val related
    (weightAbove_covers covering w)
  exact (congrArg SH.weightBlock equal).trans (weightAbove covering w).property

theorem weightAbove_surjective : Function.Surjective (weightAbove covering) := by
  intro v
  obtain ⟨w, related⟩ := covering.nonempty_fibre v
  exact ⟨w, (weightAbove_eq_iff covering v w).mpr related⟩

theorem weightAbove_fibre_card (v : SH.Fibre bH) :
    Nat.card {w : SX.Fibre bX // weightAbove covering w = v} =
      Nat.card {w : SX.Fibre bX //
        TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w.val} :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun w => weightAbove_eq_iff covering v w))

include covering literalX principalX in
/-- Each represented covered fibre is a quotient of the finite actual
ambient group. No prior finiteness of all lower weights is needed. -/
theorem coveredFibre_finite (v : SH.Fibre bH) :
    Finite {w : SX.Fibre bX //
      TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w.val} := by
  obtain ⟨w, covered⟩ := covering.nonempty_fibre v
  let f : A → {w' : SX.Fibre bX //
      TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w'.val} := fun h =>
    ⟨weightAction G SX literalX bX principalX h w,
      (covering.covered_orbit v w _ covered).mpr ⟨h, rfl⟩⟩
  apply Finite.of_surjective f
  intro w'
  obtain ⟨h, values⟩ := (covering.covered_orbit v w w'.val covered).mp w'.property
  exact ⟨h, Subtype.ext (Subtype.ext values)⟩

include covering literalX principalX in
/-- Finiteness of the lower weights follows from the finite upper set
and the actual orbit fibres. Their one/two cardinalities are derived later. -/
theorem weightAbove_finite [Finite (SH.Fibre bH)] : Finite (SX.Fibre bX) := by
  letI (v : SH.Fibre bH) : Finite {w : SX.Fibre bX // weightAbove covering w = v} := by
    letI := coveredFibre_finite covering literalX principalX v
    exact Finite.of_equiv {w : SX.Fibre bX //
      TypeBWeightCoveringSplittingSource.CoversClass G dgn v.val w.val}
      (Equiv.subtypeEquivRight (fun w => weightAbove_eq_iff covering v w)).symm
  exact Finite.of_equiv (Σ v : SH.Fibre bH,
    {w : SX.Fibre bX // weightAbove covering w = v}) (Equiv.sigmaFiberEquiv _)

include covering in
theorem weight_union (v : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := A)) :
    SH.weightBlock v = bH ↔ ∃ w : SX.Fibre bX,
      TypeBWeightCoveringSplittingSource.CoversClass G dgn v w.val := by
  constructor
  · intro principal
    obtain ⟨w, equal⟩ := weightAbove_surjective covering ⟨v, principal⟩
    exact ⟨w, (weightAbove_eq_iff covering ⟨v, principal⟩ w).mp equal⟩
  · rintro ⟨w, related⟩
    exact principal_above covering v w related

theorem weightAbove_orbit (w w' : SX.Fibre bX) :
    weightAbove covering w = weightAbove covering w' ↔
      ∃ h : A, weightAction G SX literalX bX principalX h w = w' := by
  have values := covering.covered_orbit (weightAbove covering w) w w'
    (weightAbove_covers covering w)
  rw [← weightAbove_eq_iff covering (weightAbove covering w) w'] at values
  constructor
  · intro equal
    obtain ⟨h, same⟩ := values.mp equal.symm
    exact ⟨h, Subtype.ext same⟩
  · rintro ⟨h, same⟩
    exact (values.mpr ⟨h, congrArg Subtype.val same⟩).symm

end PhysicalCovering

section QuotientLinear

variable {k K A : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k]
  [CharZero K] [Group A] [Finite A]
  (G : Subgroup A) [G.Normal] (indexTwo : G.index = 2)
  (rootH : PrimeRegularRootEmbedding 2 k K A)

include indexTwo in
/-- The actual pointwise tensor graph is the identity; no tensor-product
formula for arbitrary representations is assumed. -/
theorem quotientLinear_pointwise (lambda : linearCharactersTrivialOn (k := k) G)
    (Phi : IBr rootH) :
    PrimeRegularClassFunction.pointwiseMul (rootH.liftedLinearCharacter lambda.val) Phi.val =
      Phi.val := by
  rw [TypeBPrincipalCommonTrivialTwist.linearCharacter_eq_one G indexTwo lambda]
  change PrimeRegularClassFunction.pointwiseMul
    (rootH.liftedLinearCharacter (1 : A →* kˣ)) Phi.val = Phi.val
  rw [PrimeRegularRootEmbedding.liftedLinearCharacter_one]
  ext x
  exact one_mul (Phi.val x)

end QuotientLinear

section ActualAllRank

open TypeBCliffordCarriers TypeBAllRankPrincipalCriterionCarriers

variable {n r f : ℕ} {F k K O : Type} [Field F] [Finite F] [CharP F r]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [CommRing O] [IsDomain O] [Algebra O K]
  (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters (rank3 rank) N)
  (S : FieldActionSource n F r f parameters N)
  (SX : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K) (X n F))
  (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
  (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
  (bX : LiteralPrimitiveBlock k (X n F)) (principalX : IsPrincipal bX)
  (SH : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K) (H n F))
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (rootH : PrimeRegularRootEmbedding 2 k K (H n F))
  (bH : LiteralPrimitiveBlock k (H n F)) (principalH : IsPrincipal bH)
  (roots : RootAgreement (G n F) rootH rootX)
  (coefficient : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G n F) rootH rootX roots coefficient
    (quotient_isTwoGroup (G n F) (omega_index_two parameters rank N C)))
  (principalLift : PrincipalLiftSource (G n F) rootH rootX roots coefficient
    (quotient_isTwoGroup (G n F) (omega_index_two parameters rank N C)))
  (clifford : Clifford85_87Source (G n F) rootH rootX roots coefficient)
  (principalRestriction : PrincipalRestrictionSource (G n F) rootH rootX roots coefficient)
  (Msys : ModularSystem 2 K O k) [HasEnoughRootsOfUnity K (Nat.card (H n F))]
  (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G n F) Msys)
  (covering : PublishedPrincipalCovering (G n F) SX bX SH bH Msys dgn)

local notation "idx" => omega_index_two parameters rank N C
local notation "fieldH" => fieldAction parameters rank N C S
local notation "fieldX" => omegaAction parameters rank N C S
local notation "natural" => matrixNaturalAction parameters rank N C S
local notation "lift" => TypeBPrincipalCommonTrivialTwist.radicalLift (G n F) idx rootH

include literalX principalX principalH roots coefficient green principalLift clifford
  principalRestriction covering in
/-- Actual upper construction for every rank at least four. Lower fixation
is an internal input from the accepted selector and calibrated central
inflation; upper weight fixation is the independent FYZ field theorem.
The application supplies all counts on these same specified carriers.
The lower Brauer count can be derived from the accepted rational-class
count, its explicit partition formula, and principal central inflation.
No matching, covariance, or matched-inertia equality occurs as a premise. -/
theorem exists_upperCorrespondence
    (soBrauerCount : Nat.card (BrauerFibre rootH bH) = U n)
    (soWeightCount : Nat.card (SH.Fibre bH) = U n)
    (omegaBrauerCount : Nat.card (BrauerFibre rootX bX) = U n + D n)
    (weightDoubleCount : Nat.card {v : SH.Fibre bH //
      Nat.card {w : SX.Fibre bX //
        TypeBWeightCoveringSplittingSource.CoversClass (G n F) dgn v.val w.val} = 2} = D n)
    (omegaFixed : ∀ (e : FieldGroup f) (theta : BrauerFibre rootX bX),
      IrreducibleBrauerCharacter.twist rootX theta.val (fieldX e) = theta.val)
    (weightFixed : ∀ (e : FieldGroup f) (v : SH.Fibre bH),
      CharacterWeight.rightTwistConjugacyClass (fieldH e) v.val = v.val) :
    ∃ upper : TypeBAllRankPrincipalCriterionFixedBlockSource.UpperCorrespondence
        (G n F) fieldH rootH SH bH lift,
      (∀ (Phi : BrauerFibre rootH bH) (theta : BrauerFibre rootX bX) (w : SX.Fibre bX),
        BrauerOccursInRestriction (G n F) rootH rootX Phi.val theta.val →
        TypeBWeightCoveringSplittingSource.CoversClass (G n F) dgn
          (upper.omega Phi).val w.val →
        TypeBCriterionHypotheses.brauerMInertia (G n F) fieldH natural rootX theta.val =
          TypeBCriterionHypotheses.weightMInertia (G n F) fieldH natural w.val) ∧
      (∀ (Phi : BrauerFibre rootH bH) (V : CharacterWeight 2 K (H n F)),
        TypeBWeightCoveringSource.rawClass V = (upper.omega Phi).val →
        letI := SH.operations.ambientBlockData.fintypeBlock
        TypeBCentralKernelBrauerBlocks.block rootH (physicalDecomposition SH literalH) Phi.val =
          SH.operations.induceToAmbient V) := by
  classical
  letI : Finite (SH.Fibre bH) := Nat.finite_of_card_ne_zero (by
    rw [soWeightCount]
    exact (U_pos n).ne')
  letI : Finite (SX.Fibre bX) := weightAbove_finite covering literalX principalX
  let q := principalAbove (G n F) rootX bX principalX rootH bH principalH
    roots coefficient idx green principalLift
  let t := weightAbove covering
  have upperX : Fintype.card (BrauerFibre rootH bH) = U n := by
    simpa only [← Nat.card_eq_fintype_card] using soBrauerCount
  have upperY : Fintype.card (SH.Fibre bH) = U n := by
    simpa only [← Nat.card_eq_fintype_card] using soWeightCount
  have lowerX : Fintype.card (BrauerFibre rootX bX) = U n + D n := by
    simpa only [← Nat.card_eq_fintype_card] using omegaBrauerCount
  have doubleY : Fintype.card {v : SH.Fibre bH //
      Fintype.card {w : SX.Fibre bX // t w = v} = 2} = D n := by
    rw [← Nat.card_eq_fintype_card]
    calc
      Nat.card {v : SH.Fibre bH // Fintype.card {w : SX.Fibre bX // t w = v} = 2} =
          Nat.card {v : SH.Fibre bH // Nat.card {w : SX.Fibre bX //
            TypeBWeightCoveringSplittingSource.CoversClass (G n F) dgn v.val w.val} = 2} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro v
        rw [← Nat.card_eq_fintype_card]
        exact Iff.of_eq (congrArg (fun a : ℕ => a = 2) (weightAbove_fibre_card covering v))
      _ = D n := weightDoubleCount
  obtain ⟨E, matched⟩ := exists_matching_of_counts (G n F) idx
    (brauerAction (G n F) SX literalX rootX bX principalX)
    (weightAction (G n F) SX literalX bX principalX)
    (brauerAction_base (G n F) SX literalX rootX bX principalX)
    (weightAction_base (G n F) SX literalX bX principalX) q t
    (principalAbove_orbit (G n F) SX literalX rootX bX principalX rootH bH principalH
      roots coefficient idx green principalLift clifford)
    (weightAbove_orbit covering literalX principalX)
    (principalAbove_surjective (G n F) rootX bX principalX rootH bH principalH
      roots coefficient idx green principalLift clifford principalRestriction)
    (weightAbove_surjective covering) (U n) (D n) upperX upperY lowerX doubleY
  have soFixed (e : FieldGroup f) (Phi : BrauerFibre rootH bH) :
      IrreducibleBrauerCharacter.twist rootH Phi.val (fieldH e) = Phi.val :=
    upper_fixed_of_lower_fixed (G n F) SX literalX rootX bX principalX rootH bH principalH
      roots coefficient idx green principalLift clifford principalRestriction SH literalH
      (fieldH e) (fieldX e) (fun _ => rfl) (omegaFixed e) Phi
  let upper : TypeBAllRankPrincipalCriterionFixedBlockSource.UpperCorrespondence
      (G n F) fieldH rootH SH bH lift := {
    lift_value := fun _ => rfl
    omega := E
    field_supported := fun e Phi => (soFixed e Phi).symm ▸ Phi.property
    field_covariant := by
      intro e Phi Psi values
      have same : Psi = Phi := Subtype.ext (values.trans (soFixed e Phi))
      exact (congrArg (fun v => (E v).val) same).trans (weightFixed e (E Phi)).symm
    linear_supported := by
      intro lambda Phi
      exact ⟨Phi, (quotientLinear_pointwise (G n F) idx rootH lambda Phi.val).symm⟩
    linear_covariant := by
      intro lambda Phi Psi values
      have same : Psi = Phi := Subtype.ext (Subtype.ext
        (values.trans (quotientLinear_pointwise (G n F) idx rootH lambda Phi.val)))
      exact (congrArg (fun v => (E v).val) same).trans
        (TypeBPrincipalCommonTrivialTwist.weightClass_twist_eq_self
          (G n F) idx rootH lambda (E Phi).val).symm }
  refine ⟨upper, ?_, ?_⟩
  · intro Phi theta w occurs covered
    have qPhi : q theta = Phi := principalAbove_eq (G n F) rootX bX principalX rootH bH
      principalH roots coefficient idx green principalLift theta Phi occurs
    have tPhi : t w = E Phi := (weightAbove_eq_iff covering (E Phi) w).mpr covered
    have same : t w = E (q theta) := tPhi.trans (congrArg E qPhi).symm
    change (MulAction.stabilizer (MulAut (G n F))ᵐᵒᵖ theta.val).comap
        ((CyclicOuterLemma37Concrete.inverseOpHom (natural).hom).comp
          SemidirectProduct.inl) =
      (MulAction.stabilizer (MulAut (G n F))ᵐᵒᵖ w.val).comap
        ((CyclicOuterLemma37Concrete.inverseOpHom (natural).hom).comp
          SemidirectProduct.inl)
    rw [matrixNaturalAction_on_SO parameters rank N C S]
    ext h
    change (conjugationOp (G n F) h • theta.val = theta.val) ↔
      conjugationOp (G n F) h • w.val = w.val
    constructor
    · intro fixed
      exact congrArg Subtype.val ((matched theta w same h).mp (Subtype.ext fixed))
    · intro fixed
      exact congrArg Subtype.val ((matched theta w same h).mpr (Subtype.ext fixed))
  · intro Phi V represents
    exact TypeBPrincipalUpperPairBlockBinding.upperPair_sameBlock
      SH literalH rootH bH Phi (E Phi) V represents

end ActualAllRank

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionUpperCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
