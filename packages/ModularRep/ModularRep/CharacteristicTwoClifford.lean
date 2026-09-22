import ModularRep.OddOrderPower
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Characteristic-two Clifford stabilisers

This file formalises the finite argument in manuscript Lemma 4.6.  The
representation theory is exposed through four source-shaped interfaces:
the Clifford constituent orbit, the equivariant Clifford correspondence,
Gallagher's linear-twist theorem, and oddness of the group of linear Brauer
twists in characteristic two.  From these inputs, Lean proves the odd-square
step and transfers an elementwise stabiliser factorisation from a constituent
to the original Brauer character.

The file does not construct Brauer characters or prove the four source
interfaces.  It also represents the effective conjugation quotient by an
explicit homomorphism whose kernel acts trivially on the selected Clifford
fibre.  Identifying that abstract action with the quotient
`H-tilde / (H * C_(H-tilde)(H))` remains an instantiation obligation.
-/

namespace ModularRep.ManuscriptVerification.CharacteristicTwoClifford

variable {L X : Type*} [Group L] [Finite L] [MulAction L X]

theorem smul_eq_self_of_sq_smul_eq_self_of_odd_card
    (hOdd : Odd (Nat.card L)) {lambda : L} {x : X}
    (hsq : lambda ^ 2 • x = x) :
    lambda • x = x := by
  let K := MulAction.stabilizer L x
  have hlambdaSq : lambda ^ 2 ∈ K := hsq
  have hKOdd : Odd (Nat.card K) :=
    hOdd.of_dvd_nat K.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ :=
    (pow_two_bijective_of_odd_card (G := K) hKOdd).surjective
      ⟨lambda ^ 2, hlambdaSq⟩
  have hkcoe : (k : L) ^ 2 = lambda ^ 2 := by
    exact congrArg Subtype.val hk
  have hklambda : (k : L) = lambda :=
    (pow_two_bijective_of_odd_card (G := L) hOdd).injective hkcoe
  exact hklambda ▸ k.property

section SourceInterfaces

variable {A E H Psi Theta Eta : Type*}
variable [Group A] [Group E] [Group H]
variable [MulAction A Psi] [MulAction E Psi]
variable [MulAction A Theta] [MulAction E Theta]
variable [MulAction A Eta] [MulAction E Eta]

/-- Source-shaped form of the Clifford-theoretic assertion that the
constituents of a restricted irreducible character form one inner orbit. -/
structure CliffordConstituentOrbit
    (inner : H →* A) (psi : Psi) (theta : Theta) where
  Constituent : Psi → Theta → Prop
  chosen : Constituent psi theta
  equivariant_A : ∀ (a : A) (p : Psi) (t : Theta),
    Constituent p t → Constituent (a • p) (a • t)
  equivariant_E : ∀ (e : E) (p : Psi) (t : Theta),
    Constituent p t → Constituent (e • p) (e • t)
  single_inner_orbit :
    ∀ t₁ t₂, Constituent psi t₁ → Constituent psi t₂ →
      ∃ h : H, inner h • t₁ = t₂

/-- Source-shaped equivariant Clifford correspondence on characters lying
over the chosen constituent.  It is entirely relational: no induction map is
postulated on characters outside the Clifford fibre. -/
structure EquivariantCliffordCorrespondence
    (psi : Psi) (theta : Theta) (eta : Eta) where
  Related : Psi → Theta → Eta → Prop
  chosen : Related psi theta eta
  equivariant_A :
    ∀ (a : A) (p : Psi) (t : Theta) (u : Eta),
      Related p t u → Related (a • p) (a • t) (a • u)
  equivariant_E :
    ∀ (e : E) (p : Psi) (t : Theta) (u : Eta),
      Related p t u → Related (e • p) (e • t) (e • u)
  unique_over_chosen :
    ∀ u₁ u₂, Related psi theta u₁ → Related psi theta u₂ → u₁ = u₂
  unique_induced :
    ∀ (p₁ p₂ : Psi) (t : Theta) (u : Eta),
      Related p₁ t u → Related p₂ t u → p₁ = p₂

/-- Source-shaped Gallagher input: conjugating a correspondent over a fixed
constituent changes it by a linear Brauer twist, and the ambient action fixes
those twists. -/
structure GallagherLinearTwist
    (L : Type*) [Group L] [MulAction L Eta]
    (theta : Theta) (eta : Eta) where
  LiesOver : Theta → Eta → Prop
  chosen : LiesOver theta eta
  exists_twist : ∀ (a : A) (u : Eta), LiesOver theta u →
    a • theta = theta → ∃ lambda : L, a • u = lambda • u
  action_commutes : ∀ (a : A) (lambda : L) (u : Eta),
    a • (lambda • u) = lambda • (a • u)

/-- In characteristic two, the group of linear Brauer twists is the dual of
an odd-order quotient.  Only its resulting odd cardinality is used below. -/
def CharacteristicTwoLinearBrauerTwistGroup
    (L : Type*) [Group L] [Finite L] : Prop :=
  Odd (Nat.card L)

/-- Elementwise form of a product stabiliser factorisation. -/
def ProductStabilizerFactorization (theta : Theta) : Prop :=
  ∀ a : A, ∀ e : E,
    a • (e • theta) = theta ↔ a • theta = theta ∧ e • theta = theta

theorem adjust_to_fix_constituent
    (inner : H →* A) (psi : Psi) (theta : Theta)
    (C : CliffordConstituentOrbit (E := E) inner psi theta)
    {a : A} {e : E} (hfix : a • (e • psi) = psi) :
    ∃ h : H, (inner h * a) • (e • theta) = theta := by
  have hmoved : C.Constituent psi (a • (e • theta)) := by
    have h := C.equivariant_A a (e • psi) (e • theta)
      (C.equivariant_E e psi theta C.chosen)
    simpa [hfix] using h
  obtain ⟨h, hh⟩ := C.single_inner_orbit
    (a • (e • theta)) theta hmoved C.chosen
  exact ⟨h, by simpa only [mul_smul] using hh⟩

theorem combined_action_fixes_correspondent
    (psi : Psi) (theta : Theta) (eta : Eta)
    (C : EquivariantCliffordCorrespondence (A := A) (E := E) psi theta eta)
    {a : A} {e : E}
    (hpsi : a • (e • psi) = psi)
    (htheta : a • (e • theta) = theta) :
    a • (e • eta) = eta := by
  have hmoved := C.equivariant_A a (e • psi) (e • theta) (e • eta)
    (C.equivariant_E e psi theta eta C.chosen)
  have hmoved' : C.Related psi theta (a • (e • eta)) := by
    simpa [hpsi, htheta] using hmoved
  exact C.unique_over_chosen _ _ hmoved' C.chosen

end SourceInterfaces

section LocalOddSquare

variable {A Q L Theta Eta : Type*}
variable [Group A] [Group Q] [Group L] [Finite L]
variable [MulAction A Theta] [MulAction A Eta] [MulAction L Eta]

/-- The manuscript's local odd-square deduction.  The exponent-two
effective quotient makes the square of an inertia element act trivially.
Gallagher then expresses its first action as a linear Brauer twist, and odd
order of the twist group forces that twist itself to fix the correspondent. -/
theorem correspondent_fixed_of_effective_exponent_two
    (theta : Theta) (eta : Eta)
    (effective : A →* Q)
    (quotient_exponent_two : ∀ q : Q, q ^ 2 = 1)
    (kernel_fixes_fibre : ∀ a : A, effective a = 1 →
      a • theta = theta → a • eta = eta)
    (G : GallagherLinearTwist (A := A) (L := L) (Eta := Eta) theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    {a : A} (haTheta : a • theta = theta) :
    a • eta = eta := by
  have haSqTheta : a ^ 2 • theta = theta := by
    simp [pow_two, mul_smul, haTheta]
  have haSqKernel : effective (a ^ 2) = 1 := by
    rw [map_pow, quotient_exponent_two]
  have haSqEta : a ^ 2 • eta = eta :=
    kernel_fixes_fibre (a ^ 2) haSqKernel haSqTheta
  obtain ⟨lambda, haEta⟩ := G.exists_twist a eta G.chosen haTheta
  have htwistSq : lambda ^ 2 • eta = eta := by
    have hcompare : a ^ 2 • eta = lambda ^ 2 • eta := by
      calc
        a ^ 2 • eta = a • (a • eta) := by simp [pow_two, mul_smul]
        _ = a • (lambda • eta) := by rw [haEta]
        _ = lambda • (a • eta) := G.action_commutes a lambda eta
        _ = lambda • (lambda • eta) := by rw [haEta]
        _ = lambda ^ 2 • eta := by simp [pow_two, mul_smul]
    exact hcompare.symm.trans haSqEta
  exact haEta.trans
    (smul_eq_self_of_sq_smul_eq_self_of_odd_card hOdd htwistSq)

end LocalOddSquare

section GlobalFactorization

variable {A E H Q L Psi Theta Eta : Type*}
variable [Group A] [Group E] [Group H] [Group Q]
variable [Group L] [Finite L]
variable [MulAction A Psi] [MulAction E Psi]
variable [MulAction A Theta] [MulAction E Theta]
variable [MulAction A Eta] [MulAction E Eta] [MulAction L Eta]

/-- Kernel-checked finite argument of manuscript Lemma 4.6.  Its four
representation theoretic inputs are the constituent-orbit theorem, the
equivariant Clifford correspondence, Gallagher's linear-twist theorem, and
oddness of the characteristic-two linear Brauer twist group.  The remaining
hypotheses express the lemma's effective exponent-two quotient and its
assumed product inertia factorisation for the chosen constituent. -/
theorem characteristicTwoClifford_stabilizer_factorization
    (inner : H →* A)
    (psi : Psi) (theta : Theta) (eta : Eta)
    (constituents : CliffordConstituentOrbit (E := E) inner psi theta)
    (correspondence : EquivariantCliffordCorrespondence (A := A) (E := E)
      psi theta eta)
    (gallagher : GallagherLinearTwist (A := A) (L := L) (Eta := Eta)
      theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    (effective : A →* Q)
    (quotient_exponent_two : ∀ q : Q, q ^ 2 = 1)
    (kernel_fixes_fibre : ∀ a : A, effective a = 1 →
      a • theta = theta → a • eta = eta)
    (theta_factorization : ProductStabilizerFactorization (A := A) (E := E) theta)
    (inner_fixes_characters : ∀ h : H, ∀ p : Psi, inner h • p = p)
    (a : A) (e : E) :
    a • (e • psi) = psi ↔ a • psi = psi ∧ e • psi = psi := by
  constructor
  · intro hcombined
    obtain ⟨h, hthetaCombined⟩ :=
      adjust_to_fix_constituent inner psi theta constituents hcombined
    let a' : A := inner h * a
    have hpsiCombined : a' • (e • psi) = psi := by
      change (inner h * a) • (e • psi) = psi
      rw [mul_smul, hcombined, inner_fixes_characters]
    have hthetaParts := (theta_factorization a' e).mp hthetaCombined
    have ha'Theta : a' • theta = theta := hthetaParts.1
    have heTheta : e • theta = theta := hthetaParts.2
    have hetaCombined : a' • (e • eta) = eta :=
      combined_action_fixes_correspondent psi theta eta correspondence
        hpsiCombined hthetaCombined
    have ha'Eta : a' • eta = eta :=
      correspondent_fixed_of_effective_exponent_two theta eta effective
        quotient_exponent_two kernel_fixes_fibre gallagher hOdd ha'Theta
    have heEta : e • eta = eta := by
      apply (MulAction.injective a')
      exact hetaCombined.trans ha'Eta.symm
    have ha'Related := correspondence.equivariant_A a' psi theta eta
      correspondence.chosen
    have heRelated := correspondence.equivariant_E e psi theta eta
      correspondence.chosen
    have ha'Psi : a' • psi = psi := by
      have ha'RelatedAtEta :
          correspondence.Related (a' • psi) theta eta := by
        simpa only [ha'Theta, ha'Eta] using ha'Related
      exact correspondence.unique_induced
        (a' • psi) psi theta eta
        ha'RelatedAtEta correspondence.chosen
    have hePsi : e • psi = psi := by
      have heRelatedAtEta :
          correspondence.Related (e • psi) theta eta := by
        simpa only [heTheta, heEta] using heRelated
      exact correspondence.unique_induced
        (e • psi) psi theta eta
        heRelatedAtEta correspondence.chosen
    have haPsi : a • psi = psi := by
      change (inner h * a) • psi = psi at ha'Psi
      simpa only [mul_smul, inner_fixes_characters] using ha'Psi
    exact ⟨haPsi, hePsi⟩
  · rintro ⟨ha, he⟩
    rw [he, ha]

/-- Predicate-level form of
`characteristicTwoClifford_stabilizer_factorization`: the full product
stabiliser factorisation transfers from `theta` to `psi`. -/
theorem characteristicTwoClifford_productStabilizerFactorization
    (inner : H →* A)
    (psi : Psi) (theta : Theta) (eta : Eta)
    (constituents : CliffordConstituentOrbit (E := E) inner psi theta)
    (correspondence : EquivariantCliffordCorrespondence (A := A) (E := E)
      psi theta eta)
    (gallagher : GallagherLinearTwist (A := A) (L := L) (Eta := Eta)
      theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    (effective : A →* Q)
    (quotient_exponent_two : ∀ q : Q, q ^ 2 = 1)
    (kernel_fixes_fibre : ∀ a : A, effective a = 1 →
      a • theta = theta → a • eta = eta)
    (theta_factorization : ProductStabilizerFactorization (A := A) (E := E) theta)
    (inner_fixes_characters : ∀ h : H, ∀ p : Psi, inner h • p = p) :
    ProductStabilizerFactorization (A := A) (E := E) psi := by
  intro a e
  exact characteristicTwoClifford_stabilizer_factorization
    inner psi theta eta constituents correspondence gallagher hOdd effective
    quotient_exponent_two kernel_fixes_fibre theta_factorization
    inner_fixes_characters a e

end GlobalFactorization

section StabilizerRestrictedFactorization

variable {A E H Q L Psi Theta Eta : Type*}
variable [Group A] [Group E] [Group H] [Group Q]
variable [Group L] [Finite L]
variable [MulAction A Psi] [MulAction E Psi]
variable [MulAction A Theta] [MulAction E Theta]

/-- Clifford correspondence on the fixed inertia carrier attached to
`theta`.  Only the stabilisers of `theta` act on `Eta`; elements moving
`theta` are not given an artificial action on that fixed carrier. -/
structure StabilizerRestrictedCliffordCorrespondence
    (psi : Psi) (theta : Theta) (eta : Eta)
    [MulAction (MulAction.stabilizer A theta) Eta]
    [MulAction (MulAction.stabilizer E theta) Eta] where
  Related : Psi → Eta → Prop
  chosen : Related psi eta
  equivariant_A :
    ∀ (a : MulAction.stabilizer A theta) (p : Psi) (u : Eta),
      Related p u → Related ((a : A) • p) (a • u)
  equivariant_E :
    ∀ (e : MulAction.stabilizer E theta) (p : Psi) (u : Eta),
      Related p u → Related ((e : E) • p) (e • u)
  unique_over_psi :
    ∀ u₁ u₂, Related psi u₁ → Related psi u₂ → u₁ = u₂
  unique_induced :
    ∀ (p₁ p₂ : Psi) (u : Eta),
      Related p₁ u → Related p₂ u → p₁ = p₂

/-- Corrected source-shaped form of the characteristic-two Clifford
factorisation.  The ambient groups `A` and `E` act on `Psi` and `Theta`, but
the fixed inertia carrier `Eta` is acted on only by the respective
stabilisers of `theta`.

This is the concrete action shape of manuscript Lemma 4.6.  The older
all-ambient-action endpoint remains a valid abstract theorem, but it cannot
literally be instantiated with `Eta = IBr(H_theta)` unless every ambient
element normalises `H_theta`. -/
theorem characteristicTwoClifford_stabilizerRestricted_factorization
    (inner : H →* A)
    (psi : Psi) (theta : Theta) (eta : Eta)
    [MulAction (MulAction.stabilizer A theta) Eta]
    [MulAction (MulAction.stabilizer E theta) Eta]
    [MulAction L Eta]
    (constituents : CliffordConstituentOrbit (E := E) inner psi theta)
    (correspondence :
      StabilizerRestrictedCliffordCorrespondence
        (A := A) (E := E) psi theta eta)
    (gallagher :
      let _ := MulAction.compHom Theta
        (MulAction.stabilizer A theta).subtype
      GallagherLinearTwist
        (A := MulAction.stabilizer A theta) (L := L) (Eta := Eta)
        theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    (effective : MulAction.stabilizer A theta →* Q)
    (quotient_exponent_two : ∀ q : Q, q ^ 2 = 1)
    (kernel_fixes_fibre :
      ∀ a : MulAction.stabilizer A theta, effective a = 1 →
        (let _ := MulAction.compHom Theta
          (MulAction.stabilizer A theta).subtype
         a • theta = theta) →
        a • eta = eta)
    (theta_factorization :
      ProductStabilizerFactorization (A := A) (E := E) theta)
    (inner_fixes_characters : ∀ h : H, ∀ p : Psi, inner h • p = p) :
    ProductStabilizerFactorization (A := A) (E := E) psi := by
  let _ := MulAction.compHom Theta
    (MulAction.stabilizer A theta).subtype
  intro a e
  constructor
  · intro hcombined
    obtain ⟨h, hthetaCombined⟩ :=
      adjust_to_fix_constituent inner psi theta constituents hcombined
    let a' : A := inner h * a
    have hpsiCombined : a' • (e • psi) = psi := by
      change (inner h * a) • (e • psi) = psi
      rw [mul_smul, hcombined, inner_fixes_characters]
    have hthetaParts := (theta_factorization a' e).mp hthetaCombined
    have ha'Theta : a' • theta = theta := hthetaParts.1
    have heTheta : e • theta = theta := hthetaParts.2
    let aTheta : MulAction.stabilizer A theta := ⟨a', ha'Theta⟩
    let eTheta : MulAction.stabilizer E theta := ⟨e, heTheta⟩
    have hetaCombined : aTheta • (eTheta • eta) = eta := by
      have heRelated := correspondence.equivariant_E eTheta psi eta
        correspondence.chosen
      have haeRelated := correspondence.equivariant_A aTheta
        (e • psi) (eTheta • eta) heRelated
      have haeRelatedAtPsi :
          correspondence.Related psi (aTheta • (eTheta • eta)) := by
        change correspondence.Related
          (a' • (e • psi)) (aTheta • (eTheta • eta)) at haeRelated
        rw [hpsiCombined] at haeRelated
        exact haeRelated
      exact correspondence.unique_over_psi _ _ haeRelatedAtPsi
        correspondence.chosen
    have haThetaLocal : aTheta • theta = theta := by
      exact aTheta.property
    have haEta : aTheta • eta = eta :=
      correspondent_fixed_of_effective_exponent_two theta eta effective
        quotient_exponent_two kernel_fixes_fibre gallagher hOdd haThetaLocal
    have heEta : eTheta • eta = eta := by
      apply (MulAction.injective aTheta)
      exact hetaCombined.trans haEta.symm
    have haRelated := correspondence.equivariant_A aTheta psi eta
      correspondence.chosen
    have heRelated := correspondence.equivariant_E eTheta psi eta
      correspondence.chosen
    have ha'Psi : a' • psi = psi := by
      have haRelatedAtEta : correspondence.Related (a' • psi) eta := by
        simpa only [haEta] using haRelated
      exact correspondence.unique_induced (a' • psi) psi eta
        haRelatedAtEta correspondence.chosen
    have hePsi : e • psi = psi := by
      have heRelatedAtEta : correspondence.Related (e • psi) eta := by
        simpa only [heEta] using heRelated
      exact correspondence.unique_induced (e • psi) psi eta
        heRelatedAtEta correspondence.chosen
    have haPsi : a • psi = psi := by
      change (inner h * a) • psi = psi at ha'Psi
      simpa only [mul_smul, inner_fixes_characters] using ha'Psi
    exact ⟨haPsi, hePsi⟩
  · rintro ⟨ha, he⟩
    rw [he, ha]

end StabilizerRestrictedFactorization

end ModularRep.ManuscriptVerification.CharacteristicTwoClifford


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
