import ModularRep.CharacteristicTwoClifford
import ModularRep.IrreducibleBrauerCharacter

/-!
# Characteristic-two Clifford argument for Brauer characters

This file applies the finite argument in `CharacteristicTwoClifford` to the
library's function-valued irreducible Brauer characters.  Actions of the
ambient and field groups are supplied as homomorphisms to the opposite
automorphism groups, in accordance with the manuscript's right-action
convention.

The application theorem has four representation theoretic inputs: the
Clifford constituent orbit, the equivariant Clifford correspondence,
Gallagher's linear Brauer twist theorem, and oddness of the group of linear
Brauer twists in characteristic two.  Its remaining assumptions describe the
effective exponent-two quotient, the action of its kernel on the inertia
group, and the product stabiliser factorisation for the selected constituent.
In particular, it does not assume any stabiliser factorisation for the ambient
Brauer character.
-/

noncomputable section

namespace ModularRep.ManuscriptVerification.CharacteristicTwoClifford

universe u v h n i a e q l

variable {k : Type u} {K : Type v}
variable {H : Type h} {N : Type n} {I : Type i}
variable {A : Type a} {E : Type e} {Q : Type q} {L : Type l}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group N] [Finite N] [Group I] [Finite I]
variable [Group A] [Group E] [Group Q] [Group L] [Finite L]

/-- Inner automorphisms fix function-valued irreducible Brauer characters.
This discharges the inner-invariance hypotheses in the abstract Clifford
argument from the actual automorphism action. -/
theorem op_conj_smul_irreducibleBrauerCharacter_eq
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (phi : IBr iota) (h : H) :
    MulOpposite.op (MulAut.conj h) • phi = phi := by
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact ModularRep.PrimeRegularClassFunction.twist_conj phi.1 h

/-- Manuscript Lemma 4.6 specialised to actual irreducible Brauer characters.

The six action homomorphisms are the ambient and field actions on the Brauer
characters of `H`, `N`, and the inertia group `I`.  The hypothesis
`kernel_action_on_inertia_is_inner` is the group-theoretic identification of
the kernel of the effective quotient action; once it is supplied, fixation of
the Clifford correspondent follows from inner invariance rather than being
assumed. -/
theorem brauerCharacter_productStabilizerFactorization
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (iotaI : PrimeRegularRootEmbedding 2 k K I)
    (rhoAH : A →* (MulAut H)ᵐᵒᵖ)
    (rhoAN : A →* (MulAut N)ᵐᵒᵖ)
    (rhoAI : A →* (MulAut I)ᵐᵒᵖ)
    (rhoEH : E →* (MulAut H)ᵐᵒᵖ)
    (rhoEN : E →* (MulAut N)ᵐᵒᵖ)
    (rhoEI : E →* (MulAut I)ᵐᵒᵖ)
    (linearBrauerTwists : MulAction L (IBr iotaI))
    (inner : H →* A)
    (psi : IBr iotaH) (theta : IBr iotaN) (eta : IBr iotaI)
    (constituents :
      let _ := MulAction.compHom (IBr iotaH) rhoAH
      let _ := MulAction.compHom (IBr iotaH) rhoEH
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaN) rhoEN
      CliffordConstituentOrbit (E := E) inner psi theta)
    (correspondence :
      let _ := MulAction.compHom (IBr iotaH) rhoAH
      let _ := MulAction.compHom (IBr iotaH) rhoEH
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaN) rhoEN
      let _ := MulAction.compHom (IBr iotaI) rhoAI
      let _ := MulAction.compHom (IBr iotaI) rhoEI
      EquivariantCliffordCorrespondence (A := A) (E := E) psi theta eta)
    (gallagher :
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaI) rhoAI
      let _ := linearBrauerTwists
      GallagherLinearTwist (A := A) (Eta := IBr iotaI) L theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    (effective : A →* Q)
    (quotient_exponent_two : ∀ q : Q, q ^ 2 = 1)
    (kernel_action_on_inertia_is_inner :
      ∀ a : A, effective a = 1 →
        (let _ := MulAction.compHom (IBr iotaN) rhoAN
         a • theta = theta) →
        ∃ u : I, rhoAI a = MulOpposite.op (MulAut.conj u))
    (theta_factorization :
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaN) rhoEN
      ProductStabilizerFactorization (A := A) (E := E) theta)
    (inner_fixes_characters :
      let _ := MulAction.compHom (IBr iotaH) rhoAH
      ∀ h : H, ∀ p : IBr iotaH, inner h • p = p) :
    let _ := MulAction.compHom (IBr iotaH) rhoAH
    let _ := MulAction.compHom (IBr iotaH) rhoEH
    ProductStabilizerFactorization (A := A) (E := E) psi := by
  let _ := MulAction.compHom (IBr iotaH) rhoAH
  let _ := MulAction.compHom (IBr iotaH) rhoEH
  let _ := MulAction.compHom (IBr iotaN) rhoAN
  let _ := MulAction.compHom (IBr iotaN) rhoEN
  let _ := MulAction.compHom (IBr iotaI) rhoAI
  let _ := MulAction.compHom (IBr iotaI) rhoEI
  let _ := linearBrauerTwists
  apply characteristicTwoClifford_productStabilizerFactorization
    inner psi theta eta constituents correspondence gallagher hOdd effective
      quotient_exponent_two
  · intro a ha htheta
    obtain ⟨u, hu⟩ := kernel_action_on_inertia_is_inner a ha htheta
    change rhoAI a • eta = eta
    rw [hu]
    exact op_conj_smul_irreducibleBrauerCharacter_eq iotaI eta u
  · exact theta_factorization
  · exact inner_fixes_characters

/-- The corrected function-valued application of manuscript Lemma 4.6.

Unlike `brauerCharacter_productStabilizerFactorization`, this theorem does
not give all of `A` and `E` actions on the fixed carrier `IBr iotaI`.  Only
the stabilisers of the selected constituent `theta` act there, exactly as
for the literal inertia group `H_theta`.  The remaining inputs are the
source-shaped Clifford and Gallagher statements and the concrete action
homomorphisms on the three sets of characters. -/
theorem brauerCharacter_stabilizerRestricted_productStabilizerFactorization
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (iotaI : PrimeRegularRootEmbedding 2 k K I)
    (rhoAH : A →* (MulAut H)ᵐᵒᵖ)
    (rhoAN : A →* (MulAut N)ᵐᵒᵖ)
    (rhoEH : E →* (MulAut H)ᵐᵒᵖ)
    (rhoEN : E →* (MulAut N)ᵐᵒᵖ)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (rhoAThetaI :
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      MulAction.stabilizer A theta →* (MulAut I)ᵐᵒᵖ)
    (rhoEThetaI :
      let _ := MulAction.compHom (IBr iotaN) rhoEN
      MulAction.stabilizer E theta →* (MulAut I)ᵐᵒᵖ)
    (linearBrauerTwists : MulAction L (IBr iotaI))
    (inner : H →* A)
    (eta : IBr iotaI)
    (constituents :
      let _ := MulAction.compHom (IBr iotaH) rhoAH
      let _ := MulAction.compHom (IBr iotaH) rhoEH
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaN) rhoEN
      CliffordConstituentOrbit (E := E) inner psi theta)
    (correspondence :
      let _ := MulAction.compHom (IBr iotaH) rhoAH
      let _ := MulAction.compHom (IBr iotaH) rhoEH
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaN) rhoEN
      let _ := MulAction.compHom (IBr iotaI) rhoAThetaI
      let _ := MulAction.compHom (IBr iotaI) rhoEThetaI
      StabilizerRestrictedCliffordCorrespondence
        (A := A) (E := E) psi theta eta)
    (gallagher :
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaI) rhoAThetaI
      let _ := linearBrauerTwists
      GallagherLinearTwist
        (A := MulAction.stabilizer A theta) (Eta := IBr iotaI) L theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    (effective :
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      MulAction.stabilizer A theta →* Q)
    (quotient_exponent_two : ∀ q : Q, q ^ 2 = 1)
    (kernel_action_on_inertia_is_inner :
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      ∀ a : MulAction.stabilizer A theta, effective a = 1 →
        ∃ u : I, rhoAThetaI a = MulOpposite.op (MulAut.conj u))
    (theta_factorization :
      let _ := MulAction.compHom (IBr iotaN) rhoAN
      let _ := MulAction.compHom (IBr iotaN) rhoEN
      ProductStabilizerFactorization (A := A) (E := E) theta)
    (inner_action : ∀ h : H,
      rhoAH (inner h) = MulOpposite.op (MulAut.conj h)) :
    let _ := MulAction.compHom (IBr iotaH) rhoAH
    let _ := MulAction.compHom (IBr iotaH) rhoEH
    ProductStabilizerFactorization (A := A) (E := E) psi := by
  let _ := MulAction.compHom (IBr iotaH) rhoAH
  let _ := MulAction.compHom (IBr iotaH) rhoEH
  let _ := MulAction.compHom (IBr iotaN) rhoAN
  let _ := MulAction.compHom (IBr iotaN) rhoEN
  let _ := MulAction.compHom (IBr iotaI) rhoAThetaI
  let _ := MulAction.compHom (IBr iotaI) rhoEThetaI
  let _ := linearBrauerTwists
  apply characteristicTwoClifford_stabilizerRestricted_factorization
    inner psi theta eta constituents correspondence gallagher hOdd effective
      quotient_exponent_two
  · intro a ha _
    obtain ⟨u, hu⟩ := kernel_action_on_inertia_is_inner a ha
    change rhoAThetaI a • eta = eta
    rw [hu]
    exact op_conj_smul_irreducibleBrauerCharacter_eq iotaI eta u
  · exact theta_factorization
  · intro h p
    change rhoAH (inner h) • p = p
    rw [inner_action]
    exact op_conj_smul_irreducibleBrauerCharacter_eq iotaH p h

end ModularRep.ManuscriptVerification.CharacteristicTwoClifford


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
