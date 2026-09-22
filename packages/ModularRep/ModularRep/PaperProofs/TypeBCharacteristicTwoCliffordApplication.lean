import ModularRep.CharacteristicTwoCliffordApplication
import ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordKernel
import ModularRep.PaperProofs.EvenFieldAssumption53Relative

/-!
# Carrier and action adapters for the type B Clifford step

This file connects the corrected stabiliser-restricted theorem for manuscript
Lemma 4.6 to the literal inertia group.  The ambient group acts on Brauer
characters by the manuscript's right conjugation action.  The carrier for a
Clifford correspondent is the inertia subgroup of the selected constituent,
represented inside its ambient stabiliser.  The effective homomorphism is the
literal quotient by `H C_Gamma(H)`.

Modular Clifford theory, Gallagher's theorem, and the existence of the
required extensions are not reconstructed here.  They remain source
interfaces.  The manuscript-specific deductions below identify the ambient
carrier and action, restrict an ambient field action to the inertia subgroup,
and discharge the effective-kernel fixation from the quotient calculation checked in
`TypeBCharacteristicTwoCliffordKernel`.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordApplication

open ModularRep.ManuscriptVerification.CharacteristicTwoClifford
open ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordKernel
open ModularRep.PaperProofs.EvenFieldAssumption53Relative

universe u v w x

variable {Gamma : Type u} [Group Gamma]

/-- The literal effective conjugation quotient in Lemma 4.6. -/
abbrev EffectiveConjugationQuotient
    (H : Subgroup Gamma) :=
  Gamma ⧸ effectiveConjugationKernel H

/-- Restrict the literal quotient map to the stabiliser of the selected
constituent.  Thus the kernel in the local Clifford argument is not supplied
as an unrelated abstract homomorphism. -/
def effectiveActionOnAmbientStabilizer
    {Theta : Type v} [MulAction Gamma Theta]
    (H : Subgroup Gamma) [H.Normal] (theta : Theta) :
    letI : (effectiveConjugationKernel H).Normal :=
      effectiveConjugationKernel_normal H
    MulAction.stabilizer Gamma theta →*
      EffectiveConjugationQuotient H := by
  let _ : (effectiveConjugationKernel H).Normal :=
    effectiveConjugationKernel_normal H
  exact (QuotientGroup.mk' (effectiveConjugationKernel H)).comp
    (ambientStabilizer (Gamma := Gamma) theta).subtype

/-- The right-conjugation homomorphism with source written literally as the
Lean stabiliser subtype expected by the corrected Clifford theorem. -/
def rightConjugationOnLiteralStabilizerHom
    {Theta : Type v} [MulAction Gamma Theta]
    (H : Subgroup Gamma) [H.Normal] (theta : Theta) :
    MulAction.stabilizer Gamma theta →*
      (MulAut (inertiaInAmbientStabilizer
        (Gamma := Gamma) H theta))ᵐᵒᵖ :=
  rightConjugationOnInertiaHom H theta

/-- Positive conjugation on the inertia subgroup written as a subgroup of
`H`.  This is the carrier on which an external field automorphism is most
directly restricted. -/
def conjugationOnInertiaSubgroupHom
    {Theta : Type v} [MulAction Gamma Theta]
    (H : Subgroup Gamma) [H.Normal] (theta : Theta) :
    MulAction.stabilizer Gamma theta →* MulAut (inertiaSubgroup H theta) where
  toFun a := conjugationOnInertia H theta (a : Gamma) a.property
  map_one' := by
    ext x
    change (1 : Gamma) * (x : H) * (1 : Gamma)⁻¹ = (x : H)
    simp
  map_mul' a b := by
    ext x
    change ((a : Gamma) * (b : Gamma)) * (x : H) *
        ((a : Gamma) * (b : Gamma))⁻¹ =
      (a : Gamma) * ((b : Gamma) * (x : H) * (b : Gamma)⁻¹) *
        (a : Gamma)⁻¹
    simp only [mul_inv_rev, mul_assoc]

/-- The manuscript right action on the same subgroup carrier. -/
def rightConjugationOnInertiaSubgroupHom
    {Theta : Type v} [MulAction Gamma Theta]
    (H : Subgroup Gamma) [H.Normal] (theta : Theta) :
    MulAction.stabilizer Gamma theta →*
      (MulAut (inertiaSubgroup H theta))ᵐᵒᵖ :=
  inverseOppositeHom (conjugationOnInertiaSubgroupHom H theta)

section FieldRestriction

variable {E : Type x} {Theta : Type v} [Group E]
variable [MulAction Gamma Theta] [MulAction E Theta]

/-- Restriction of a field automorphism to the inertia subgroup.  The two
hypotheses are the exact action adapters still required in the manuscript:
field automorphisms preserve `H`, and their action on `Theta` is natural with
respect to conjugation. -/
def fieldAutomorphismOnInertiaSubgroup
    (H : Subgroup Gamma) (theta : Theta)
    (field : E →* MulAut Gamma)
    (hHstable : ∀ e : E, ∀ g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (hcompat : ∀ e : E, ∀ g : Gamma, ∀ t : Theta,
      e • (g • t) = field e g • (e • t))
    (e : MulAction.stabilizer E theta) :
    MulAut (inertiaSubgroup H theta) where
  toFun x := by
    let g : Gamma := field (e : E) (x : H)
    have hgH : g ∈ H :=
      (hHstable (e : E) (x : H)).mp x.1.property
    let gH : H := ⟨g, hgH⟩
    refine ⟨gH, ?_⟩
    change g • theta = theta
    have hx : ((x : H) : Gamma) • theta = theta := by
      exact x.property
    have he : (e : E) • theta = theta := e.property
    have h := hcompat (e : E) (x : H) theta
    rw [hx, he] at h
    simpa only [g] using h.symm
  invFun x := by
    let g : Gamma := field (e : E)⁻¹ (x : H)
    have hgH : g ∈ H :=
      (hHstable (e : E)⁻¹ (x : H)).mp x.1.property
    let gH : H := ⟨g, hgH⟩
    refine ⟨gH, ?_⟩
    change g • theta = theta
    have hx : ((x : H) : Gamma) • theta = theta := by
      exact x.property
    have heInv : (e : E)⁻¹ • theta = theta :=
      (MulAction.stabilizer E theta).inv_mem e.property
    have h := hcompat (e : E)⁻¹ (x : H) theta
    rw [hx, heInv] at h
    simpa only [g] using h.symm
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change field (e : E)⁻¹ (field (e : E) ((x : H) : Gamma)) =
      ((x : H) : Gamma)
    rw [map_inv]
    exact (field (e : E)).symm_apply_apply ((x : H) : Gamma)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change field (e : E) (field (e : E)⁻¹ ((x : H) : Gamma)) =
      ((x : H) : Gamma)
    rw [map_inv]
    exact (field (e : E)).apply_symm_apply ((x : H) : Gamma)
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (field (e : E)) ((x : H) : Gamma) ((y : H) : Gamma)

/-- Positive field transport on the inertia subgroup is a homomorphism. -/
def fieldAutomorphismOnInertiaSubgroupHom
    (H : Subgroup Gamma) (theta : Theta)
    (field : E →* MulAut Gamma)
    (hHstable : ∀ e : E, ∀ g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (hcompat : ∀ e : E, ∀ g : Gamma, ∀ t : Theta,
      e • (g • t) = field e g • (e • t)) :
    MulAction.stabilizer E theta →* MulAut (inertiaSubgroup H theta) where
  toFun e := fieldAutomorphismOnInertiaSubgroup
    H theta field hHstable hcompat e
  map_one' := by
    ext x
    simp [fieldAutomorphismOnInertiaSubgroup]
  map_mul' e f := by
    ext x
    simp [fieldAutomorphismOnInertiaSubgroup]

/-- The induced field action on `IBr(H_theta)` in the manuscript's right
action orientation.  No separate local action homomorphism is now needed once
the two naturality inputs above are supplied. -/
def fieldRightActionOnInertiaSubgroupHom
    (H : Subgroup Gamma) (theta : Theta)
    (field : E →* MulAut Gamma)
    (hHstable : ∀ e : E, ∀ g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (hcompat : ∀ e : E, ∀ g : Gamma, ∀ t : Theta,
      e • (g • t) = field e g • (e • t)) :
    MulAction.stabilizer E theta →*
      (MulAut (inertiaSubgroup H theta))ᵐᵒᵖ :=
  inverseOppositeHom
    (fieldAutomorphismOnInertiaSubgroupHom H theta field hHstable hcompat)

end FieldRestriction

section BrauerConstituent

variable {k : Type v} {K : Type w}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Finite Gamma]

/-- An element centralising `H` fixes every Brauer character of a normal
subgroup `N ≤ H` under the literal right conjugation action.  This is the
action-specific premise needed by the effective-kernel theorem. -/
theorem centralizer_fixes_brauer_constituent
    (H N : Subgroup Gamma) [H.Normal] [N.Normal]
    (hNH : N ≤ H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) :
    let _ : MulAction Gamma (IBr iotaN) :=
      rightAutomorphismAction iotaN (MulAut.conjNormal (H := N))
    ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta := by
  dsimp only
  intro c hc
  change IrreducibleBrauerCharacter.twist iotaN theta
    (MulAut.conjNormal (H := N) c⁻¹) = theta
  have hcInv : c⁻¹ ∈ Subgroup.centralizer (H : Set Gamma) :=
    (Subgroup.centralizer (H : Set Gamma)).inv_mem hc
  have hAut : MulAut.conjNormal (H := N) c⁻¹ = MulEquiv.refl N := by
    ext n
    have hcomm : c⁻¹ * (n : Gamma) = (n : Gamma) * c⁻¹ :=
      ((Subgroup.mem_centralizer_iff.mp hcInv) (n : Gamma) (hNH n.property)).symm
    change c⁻¹ * (n : Gamma) * (c⁻¹)⁻¹ = (n : Gamma)
    rw [hcomm]
    simp
  rw [hAut]
  exact IrreducibleBrauerCharacter.twist_refl iotaN theta

section LiteralInertiaCharacter

variable {Theta : Type x} [MulAction Gamma Theta]

/-- The literal effective kernel fixes every Brauer character of the inertia
group.  Kernel membership is converted to an inner right-conjugation action
by `rightConjugationOnInertiaHom_inner_of_quotient_eq_one`; class-function
invariance then supplies the final equality. -/
theorem effectiveKernel_fixes_inertia_brauer_character
    (H : Subgroup Gamma) [H.Normal] (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (iotaI : PrimeRegularRootEmbedding 2 k K
      (inertiaInAmbientStabilizer (Gamma := Gamma) H theta))
    (eta : IBr iotaI) :
    letI : (effectiveConjugationKernel H).Normal :=
      effectiveConjugationKernel_normal H
    let rhoI := rightConjugationOnLiteralStabilizerHom H theta
    let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
      MulAction.compHom (IBr iotaI) rhoI
    ∀ a : MulAction.stabilizer Gamma theta,
      effectiveActionOnAmbientStabilizer H theta a = 1 → a • eta = eta := by
  dsimp only
  let _ : (effectiveConjugationKernel H).Normal :=
    effectiveConjugationKernel_normal H
  let rhoI := rightConjugationOnLiteralStabilizerHom H theta
  let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
    MulAction.compHom (IBr iotaI) rhoI
  intro a ha
  obtain ⟨h, hh⟩ :=
    rightConjugationOnInertiaHom_inner_of_quotient_eq_one
      H theta centralizer_fixes a ha
  change (rightConjugationOnInertiaHom H theta) a • eta = eta
  rw [hh]
  exact op_conj_smul_irreducibleBrauerCharacter_eq iotaI eta h

/-- The same kernel-fixation result on the conventional carrier
`H_theta ≤ H`. -/
theorem effectiveKernel_fixes_inertiaSubgroup_brauer_character
    (H : Subgroup Gamma) [H.Normal] (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (iotaI : PrimeRegularRootEmbedding 2 k K (inertiaSubgroup H theta))
    (eta : IBr iotaI) :
    letI : (effectiveConjugationKernel H).Normal :=
      effectiveConjugationKernel_normal H
    let rhoI := rightConjugationOnInertiaSubgroupHom H theta
    let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
      MulAction.compHom (IBr iotaI) rhoI
    ∀ a : MulAction.stabilizer Gamma theta,
      effectiveActionOnAmbientStabilizer H theta a = 1 → a • eta = eta := by
  dsimp only
  let _ : (effectiveConjugationKernel H).Normal :=
    effectiveConjugationKernel_normal H
  let rhoI := rightConjugationOnInertiaSubgroupHom H theta
  let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
    MulAction.compHom (IBr iotaI) rhoI
  intro a ha
  obtain ⟨h, hh⟩ :=
    op_inverse_conjugationOnInertia_eq_inner_of_quotient_eq_one
      H theta centralizer_fixes (a : Gamma) ha a.property
  have hrho : rhoI a = MulOpposite.op
      ((conjugationOnInertia H theta (a : Gamma) a.property)⁻¹) := by
    have hmap := map_inv (conjugationOnInertiaSubgroupHom H theta) a
    change MulOpposite.op
        ((conjugationOnInertiaSubgroupHom H theta) a⁻¹) =
      MulOpposite.op
        (((conjugationOnInertiaSubgroupHom H theta) a)⁻¹)
    exact congrArg MulOpposite.op hmap
  change rhoI a • eta = eta
  rw [hrho, hh]
  exact op_conj_smul_irreducibleBrauerCharacter_eq iotaI eta h

/-- Function-valued Lemma 4.6 with the local side instantiated by the literal
inertia group.  The ambient and field actions on `psi` and `theta` remain
explicit inputs, but only their stabilisers of `theta` act on the fixed
carrier `IBr(H_theta)`.  On the ambient side that local action and the
effective quotient are now the literal ones. -/
theorem literalInertia_brauerCharacter_productStabilizerFactorization
    {E L : Type x} [Group E] [Group L] [Finite L]
    (H N : Subgroup Gamma) [H.Normal] [N.Normal]
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    [MulAction Gamma (IBr iotaH)] [MulAction E (IBr iotaH)]
    [MulAction Gamma (IBr iotaN)] [MulAction E (IBr iotaN)]
    (psi : IBr iotaH) (theta : IBr iotaN)
    (iotaI : PrimeRegularRootEmbedding 2 k K
      (inertiaInAmbientStabilizer (Gamma := Gamma) H theta))
    (rhoEThetaI : MulAction.stabilizer E theta →*
      (MulAut (inertiaInAmbientStabilizer
        (Gamma := Gamma) H theta))ᵐᵒᵖ)
    (linearBrauerTwists : MulAction L (IBr iotaI))
    (eta : IBr iotaI)
    (constituents : CliffordConstituentOrbit (E := E) H.subtype psi theta)
    (correspondence :
      letI := MulAction.compHom (IBr iotaI)
        (rightConjugationOnLiteralStabilizerHom H theta)
      letI := MulAction.compHom (IBr iotaI) rhoEThetaI
      StabilizerRestrictedCliffordCorrespondence
        (A := Gamma) (E := E) psi theta eta)
    (gallagher :
      letI := MulAction.compHom (IBr iotaI)
        (rightConjugationOnLiteralStabilizerHom H theta)
      letI := linearBrauerTwists
      GallagherLinearTwist
        (A := MulAction.stabilizer Gamma theta)
        (Eta := IBr iotaI) L theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (quotient_exponent_two :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      ∀ q : EffectiveConjugationQuotient H, q ^ 2 = 1)
    (theta_factorization :
      ProductStabilizerFactorization (A := Gamma) (E := E) theta)
    (inner_fixes_characters : ∀ h : H, ∀ p : IBr iotaH,
      (h : Gamma) • p = p) :
    ProductStabilizerFactorization (A := Gamma) (E := E) psi := by
  let rhoAI := rightConjugationOnLiteralStabilizerHom H theta
  let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
    MulAction.compHom (IBr iotaI) rhoAI
  let _ : MulAction (MulAction.stabilizer E theta) (IBr iotaI) :=
    MulAction.compHom (IBr iotaI) rhoEThetaI
  let _ := linearBrauerTwists
  let _ : (effectiveConjugationKernel H).Normal :=
    effectiveConjugationKernel_normal H
  apply characteristicTwoClifford_stabilizerRestricted_factorization
    H.subtype psi theta eta constituents correspondence gallagher hOdd
      (effectiveActionOnAmbientStabilizer H theta) quotient_exponent_two
  · intro a ha _
    exact effectiveKernel_fixes_inertia_brauer_character
      H theta centralizer_fixes iotaI eta a ha
  · exact theta_factorization
  · exact inner_fixes_characters

/-- Lemma 4.6 on the conventional inertia subgroup `H_theta ≤ H`, with
the local field action constructed from a field automorphism of the ambient
group.  Thus the local `E_theta` action is no longer an independent source
input: it follows from preservation of `H` and naturality of the action on
the selected constituent. -/
theorem inertiaSubgroupWithField_brauerCharacter_productStabilizerFactorization
    {E L : Type x} [Group E] [Group L] [Finite L]
    (H N : Subgroup Gamma) [H.Normal] [N.Normal]
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    [MulAction Gamma (IBr iotaH)] [MulAction E (IBr iotaH)]
    [MulAction Gamma (IBr iotaN)] [MulAction E (IBr iotaN)]
    (psi : IBr iotaH) (theta : IBr iotaN)
    (iotaI : PrimeRegularRootEmbedding 2 k K (inertiaSubgroup H theta))
    (field : E →* MulAut Gamma)
    (hHstable : ∀ e : E, ∀ g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (hcompat : ∀ e : E, ∀ g : Gamma, ∀ t : IBr iotaN,
      e • (g • t) = field e g • (e • t))
    (linearBrauerTwists : MulAction L (IBr iotaI))
    (eta : IBr iotaI)
    (constituents : CliffordConstituentOrbit (E := E) H.subtype psi theta)
    (correspondence :
      letI := MulAction.compHom (IBr iotaI)
        (rightConjugationOnInertiaSubgroupHom H theta)
      letI := MulAction.compHom (IBr iotaI)
        (fieldRightActionOnInertiaSubgroupHom
          H theta field hHstable hcompat)
      StabilizerRestrictedCliffordCorrespondence
        (A := Gamma) (E := E) psi theta eta)
    (gallagher :
      letI := MulAction.compHom (IBr iotaI)
        (rightConjugationOnInertiaSubgroupHom H theta)
      letI := linearBrauerTwists
      GallagherLinearTwist
        (A := MulAction.stabilizer Gamma theta)
        (Eta := IBr iotaI) L theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup L)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (quotient_exponent_two :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      ∀ q : EffectiveConjugationQuotient H, q ^ 2 = 1)
    (theta_factorization :
      ProductStabilizerFactorization (A := Gamma) (E := E) theta)
    (inner_fixes_characters : ∀ h : H, ∀ p : IBr iotaH,
      (h : Gamma) • p = p) :
    ProductStabilizerFactorization (A := Gamma) (E := E) psi := by
  let rhoAI := rightConjugationOnInertiaSubgroupHom H theta
  let rhoEI := fieldRightActionOnInertiaSubgroupHom
    H theta field hHstable hcompat
  let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
    MulAction.compHom (IBr iotaI) rhoAI
  let _ : MulAction (MulAction.stabilizer E theta) (IBr iotaI) :=
    MulAction.compHom (IBr iotaI) rhoEI
  let _ := linearBrauerTwists
  let _ : (effectiveConjugationKernel H).Normal :=
    effectiveConjugationKernel_normal H
  apply characteristicTwoClifford_stabilizerRestricted_factorization
    H.subtype psi theta eta constituents correspondence gallagher hOdd
      (effectiveActionOnAmbientStabilizer H theta) quotient_exponent_two
  · intro a ha _
    exact effectiveKernel_fixes_inertiaSubgroup_brauer_character
      H theta centralizer_fixes iotaI eta a ha
  · exact theta_factorization
  · exact inner_fixes_characters

end LiteralInertiaCharacter

end BrauerConstituent

end ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
