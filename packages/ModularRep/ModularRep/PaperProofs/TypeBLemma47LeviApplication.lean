import ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordApplication
import ModularRep.BrauerQuotientLinearCharacterAction
import Formalisation.ComponentReturnAssembly

/-!
# The two Levi applications of the characteristic-two Clifford lemma

This file specialises manuscript Lemma 4.6 to the subgroup chain used in
both of its later applications.  In manuscript notation, `Gamma` is
`L_tilde`, `H` is `L`, `N` is `L_0`, and `E` is `D_O`.  Lean constructs the
conjugation actions on the actual function-valued Brauer characters and
restricts the supplied field automorphisms to all three relevant groups.

The literal group of Gallagher twists is the group of modular linear
characters of the inertia group that are trivial on the copy of `N` inside
it.  Modular Clifford theory, modular Gallagher theory, oddness of this
finite twist group, and the extension used to invoke Gallagher remain exact
source inputs.  No stabiliser factorisation for the selected ambient
character is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLemma47LeviApplication

open ModularRep.ManuscriptVerification.CharacteristicTwoClifford
open ModularRep.PaperProofs.EvenFieldAssumption53Relative
open ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordApplication
open ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordKernel

universe u v

variable {Gamma E k K : Type u}
variable [Group Gamma] [Finite Gamma] [Group E]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

section RestrictedFieldActions

/-- Restriction of an ambient automorphism to an invariant subgroup. -/
def restrictAutomorphism
    (H : Subgroup Gamma) (alpha : MulAut Gamma)
    (hstable : forall g : Gamma, g ∈ H ↔ alpha g ∈ H) : MulAut H where
  toFun g := ⟨alpha g, (hstable g).mp g.property⟩
  invFun g := ⟨alpha.symm g, by
    apply (hstable (alpha.symm g)).mpr
    simpa using g.property⟩
  left_inv g := by
    apply Subtype.ext
    exact alpha.symm_apply_apply g
  right_inv g := by
    apply Subtype.ext
    exact alpha.apply_symm_apply g
  map_mul' g h := by
    apply Subtype.ext
    change alpha ((g : Gamma) * (h : Gamma)) =
      alpha (g : Gamma) * alpha (h : Gamma)
    exact map_mul alpha (g : Gamma) (h : Gamma)

/-- A group of ambient automorphisms restricts to an invariant subgroup. -/
def restrictAutomorphismHom
    (H : Subgroup Gamma) (field : E →* MulAut Gamma)
    (hstable : forall e : E, forall g : Gamma,
      g ∈ H ↔ field e g ∈ H) : E →* MulAut H where
  toFun e := restrictAutomorphism H (field e) (hstable e)
  map_one' := by
    ext g
    change field 1 (g : Gamma) = (g : Gamma)
    simp
  map_mul' e f := by
    ext g
    change field (e * f) (g : Gamma) =
      field e (field f (g : Gamma))
    simp

@[simp]
theorem restrictAutomorphismHom_apply
    (H : Subgroup Gamma) (field : E →* MulAut Gamma)
    (hstable : forall e : E, forall g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (e : E) (g : H) :
    restrictAutomorphismHom H field hstable e g =
      ⟨field e g, (hstable e g).mp g.property⟩ :=
  rfl

/-- The literal right-conjugation action of the ambient regular Levi
overgroup on Brauer characters of a normal subgroup. -/
@[instance_reducible]
def ambientBrauerAction
    (H : Subgroup Gamma) [H.Normal]
    (iotaH : PrimeRegularRootEmbedding 2 k K H) :
    MulAction Gamma (IBr iotaH) :=
  rightAutomorphismAction iotaH (MulAut.conjNormal (H := H))

/-- The literal right field action on Brauer characters of an invariant
subgroup. -/
@[instance_reducible]
def fieldBrauerAction
    (H : Subgroup Gamma)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (field : E →* MulAut Gamma)
    (hstable : forall e : E, forall g : Gamma,
      g ∈ H ↔ field e g ∈ H) :
    MulAction E (IBr iotaH) :=
  rightAutomorphismAction iotaH
    (restrictAutomorphismHom H field hstable)

/-- Naturality of the literal field and ambient conjugation actions.  This
is the precise action identity needed to restrict a field automorphism to
the inertia group of the selected constituent. -/
theorem field_ambient_brauer_naturality
    (H : Subgroup Gamma) [H.Normal]
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (field : E →* MulAut Gamma)
    (hstable : forall e : E, forall g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (e : E) (g : Gamma) (theta : IBr iotaH) :
    let _ : MulAction Gamma (IBr iotaH) :=
      ambientBrauerAction H iotaH
    let _ : MulAction E (IBr iotaH) :=
      fieldBrauerAction H iotaH field hstable
    e • (g • theta) = field e g • (e • theta) := by
  dsimp only
  change IrreducibleBrauerCharacter.twist iotaH
      (IrreducibleBrauerCharacter.twist iotaH theta
        (MulAut.conjNormal (H := H) g⁻¹))
      (restrictAutomorphismHom H field hstable e⁻¹) =
    IrreducibleBrauerCharacter.twist iotaH
      (IrreducibleBrauerCharacter.twist iotaH theta
        (restrictAutomorphismHom H field hstable e⁻¹))
      (MulAut.conjNormal (H := H) (field e g)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul,
    IrreducibleBrauerCharacter.twist_mul]
  congr 1
  ext x
  simp [restrictAutomorphismHom, restrictAutomorphism]

/-- Elements of a normal subgroup act trivially on its own Brauer
characters, even when their action is written through a larger ambient
group. -/
theorem subgroup_element_fixes_brauer_character
    (H : Subgroup Gamma) [H.Normal]
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (h : H) (theta : IBr iotaH) :
    let _ : MulAction Gamma (IBr iotaH) :=
      ambientBrauerAction H iotaH
    (h : Gamma) • theta = theta := by
  dsimp only
  change IrreducibleBrauerCharacter.twist iotaH theta
    (MulAut.conjNormal (H := H) (h : Gamma)⁻¹) = theta
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  have hAut : MulAut.conjNormal (H := H) (h : Gamma)⁻¹ =
      MulAut.conj h⁻¹ := by
    ext x
    rfl
  rw [hAut]
  exact ModularRep.PrimeRegularClassFunction.twist_conj theta.1 h⁻¹

/-- The actual conjugation and field actions form the semidirect action
used in the notation `Gamma E` in the manuscript. -/
theorem field_ambient_semidirect_compatible
    (H : Subgroup Gamma) [H.Normal]
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (field : E →* MulAut Gamma)
    (hstable : forall e : E, forall g : Gamma,
      g ∈ H ↔ field e g ∈ H) :
    let _ : MulAction Gamma (IBr iotaH) :=
      ambientBrauerAction H iotaH
    let _ : MulAction E (IBr iotaH) :=
      fieldBrauerAction H iotaH field hstable
    Formalisation.SemidirectActionCompatible
      (X := IBr iotaH) field := by
  dsimp only
  intro e g theta
  exact field_ambient_brauer_naturality H iotaH field hstable e g theta

/-- Convert the stabiliser equality obtained from the component-return
argument, stated for the actual semidirect product, into the elementwise
factorisation required by Lemma 4.6. -/
theorem productFactorization_of_semidirectStabilizerFactors
    (H : Subgroup Gamma) [H.Normal]
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (field : E →* MulAut Gamma)
    (hstable : forall e : E, forall g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (theta : IBr iotaH)
    (hfactor :
      let _ : MulAction Gamma (IBr iotaH) :=
        ambientBrauerAction H iotaH
      let _ : MulAction E (IBr iotaH) :=
        fieldBrauerAction H iotaH field hstable
      let hcompat := field_ambient_semidirect_compatible
        H iotaH field hstable
      Formalisation.SemidirectStabilizerFactors field hcompat theta) :
    let _ : MulAction Gamma (IBr iotaH) :=
      ambientBrauerAction H iotaH
    let _ : MulAction E (IBr iotaH) :=
      fieldBrauerAction H iotaH field hstable
    ProductStabilizerFactorization (A := Gamma) (E := E) theta := by
  let _ : MulAction Gamma (IBr iotaH) :=
    ambientBrauerAction H iotaH
  let _ : MulAction E (IBr iotaH) :=
    fieldBrauerAction H iotaH field hstable
  dsimp only at hfactor ⊢
  intro g e
  let hcompat := field_ambient_semidirect_compatible
    H iotaH field hstable
  have h := hfactor (⟨g, e⟩ : Gamma ⋊[field] E)
  change (g • (e • theta) = theta ↔
    g • theta = theta ∧ e • theta = theta) at h
  exact h

end RestrictedFieldActions

section LiteralGallagherTwists

variable {Theta : Type v} [MulAction Gamma Theta]

/-- The copy of the base subgroup inside the literal inertia group.  It is
the inverse image of `N` under `H_theta -> H -> Gamma`. -/
def baseSubgroupInInertia
    (H N : Subgroup Gamma) (theta : Theta) :
    Subgroup (inertiaSubgroup H theta) :=
  N.comap (H.subtype.comp (inertiaSubgroup H theta).subtype)

/-- The literal group of modular linear characters of `H_theta/N` used by
Gallagher's theorem, represented as the characters of `H_theta` trivial on
the embedded base subgroup. -/
abbrev GallagherTwists
    (H N : Subgroup Gamma) (theta : Theta) :=
  linearCharactersTrivialOn (k := k)
    (baseSubgroupInInertia H N theta)

/-- The literal tensor action of quotient linear Brauer characters on the
Brauer characters of the inertia group. -/
@[instance_reducible]
def gallagherTwistAction
    (H N : Subgroup Gamma) (theta : Theta)
    (iotaI : PrimeRegularRootEmbedding 2 k K (inertiaSubgroup H theta))
    (productFormula : BrauerLinearTensorProductFormula iotaI) :
    MulAction (GallagherTwists (k := k) H N theta) (IBr iotaI) :=
  IrreducibleBrauerCharacter.inverseTrivialTensorAction
    iotaI productFormula

end LiteralGallagherTwists

section ActualBrauerInertia

/-- The inertia subgroup of a function-valued Brauer character for the
literal ambient conjugation action. -/
abbrev BrauerInertia
    (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) :=
  @inertiaSubgroup Gamma _ (IBr iotaN)
    (ambientBrauerAction N iotaN) H theta

/-- The embedded base subgroup in the actual Brauer-character inertia
group. -/
def baseSubgroupInBrauerInertia
    (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) : Subgroup (BrauerInertia H N iotaN theta) :=
  N.comap (H.subtype.comp (BrauerInertia H N iotaN theta).subtype)

instance baseSubgroupInBrauerInertia_normal
    (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) :
    (baseSubgroupInBrauerInertia H N iotaN theta).Normal := by
  unfold baseSubgroupInBrauerInertia
  infer_instance

/-- The literal embedding of `N` in the inertia subgroup `H_theta`.  Its
image is the subgroup used in the quotient defining the Gallagher twists. -/
def baseEmbeddingInBrauerInertia
    (H N : Subgroup Gamma) [N.Normal]
    (hNH : N ≤ H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) : N →* BrauerInertia H N iotaN theta where
  toFun n := ⟨⟨n, hNH n.property⟩, by
    exact subgroup_element_fixes_brauer_character N iotaN n theta⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The subgroup called `N` inside `H_theta` in the manuscript is exactly
the range of the literal embedding above. -/
theorem range_baseEmbeddingInBrauerInertia
    (H N : Subgroup Gamma) [N.Normal]
    (hNH : N ≤ H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) :
    (baseEmbeddingInBrauerInertia H N hNH iotaN theta).range =
      baseSubgroupInBrauerInertia H N iotaN theta := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact n.property
  · intro hx
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The actual Gallagher twist group for the selected constituent. -/
abbrev BrauerGallagherTwists
    (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) :=
  linearCharactersTrivialOn (k := k)
    (baseSubgroupInBrauerInertia H N iotaN theta)

/-- The actual Gallagher twist carrier is literally the character group of
the quotient `H_theta/N`, with `N` represented by its embedded range. -/
def brauerGallagherTwistsQuotientMulEquiv
    (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN) :
    BrauerGallagherTwists (k := k) H N iotaN theta ≃*
      (BrauerInertia H N iotaN theta ⧸
        baseSubgroupInBrauerInertia H N iotaN theta →* kˣ) :=
  LinearCharactersTrivialOn.quotientMulEquiv (k := k)
    (baseSubgroupInBrauerInertia H N iotaN theta)

/-- Tensor action of the actual Gallagher twist group on the literal
inertia carrier. -/
@[instance_reducible]
def brauerGallagherTwistAction
    (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (theta : IBr iotaN)
    (iotaI : PrimeRegularRootEmbedding 2 k K
      (BrauerInertia H N iotaN theta))
    (productFormula : BrauerLinearTensorProductFormula iotaI) :
    MulAction (BrauerGallagherTwists (k := k) H N iotaN theta)
      (IBr iotaI) :=
  IrreducibleBrauerCharacter.inverseTrivialTensorAction
    iotaI productFormula

end ActualBrauerInertia

section TwoLeviApplications

/-- Strongest common endpoint for the two concrete uses of Lemma 4.6.

The ambient and field actions on `psi` and `theta`, the inertia carrier, its
two actions, and the Gallagher twist action are all the literal ones.  The
factorisation for `theta` is supplied in the semidirect-product form proved
by the preceding component-return argument and converted here.  The only
remaining character-theoretic inputs are the exact modular Clifford and
Gallagher source instances and oddness of their literal twist group. -/
theorem leviSelectedCharacter_productStabilizerFactorization
    (H N : Subgroup Gamma) [H.Normal] [N.Normal]
    (hNH : N ≤ H)
    (iotaH : PrimeRegularRootEmbedding 2 k K H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N)
    (field : E →* MulAut Gamma)
    (hHstable : forall e : E, forall g : Gamma,
      g ∈ H ↔ field e g ∈ H)
    (hNstable : forall e : E, forall g : Gamma,
      g ∈ N ↔ field e g ∈ N)
    (psi : IBr iotaH) (theta : IBr iotaN)
    (iotaI : PrimeRegularRootEmbedding 2 k K
      (BrauerInertia H N iotaN theta))
    (productFormula : BrauerLinearTensorProductFormula iotaI)
    [Finite (BrauerGallagherTwists (Gamma := Gamma) (k := k) (K := K)
      H N iotaN theta)]
    (eta : IBr iotaI)
    (constituents :
      let _ : MulAction Gamma (IBr iotaH) :=
        ambientBrauerAction H iotaH
      let _ : MulAction E (IBr iotaH) :=
        fieldBrauerAction H iotaH field hHstable
      let _ : MulAction Gamma (IBr iotaN) :=
        ambientBrauerAction N iotaN
      let _ : MulAction E (IBr iotaN) :=
        fieldBrauerAction N iotaN field hNstable
      CliffordConstituentOrbit (E := E) H.subtype psi theta)
    (correspondence :
      let _ : MulAction Gamma (IBr iotaH) :=
        ambientBrauerAction H iotaH
      let _ : MulAction E (IBr iotaH) :=
        fieldBrauerAction H iotaH field hHstable
      let _ : MulAction Gamma (IBr iotaN) :=
        ambientBrauerAction N iotaN
      let _ : MulAction E (IBr iotaN) :=
        fieldBrauerAction N iotaN field hNstable
      let rhoAI := rightConjugationOnInertiaSubgroupHom H theta
      let rhoEI := fieldRightActionOnInertiaSubgroupHom H theta field
        hHstable (field_ambient_brauer_naturality
          N iotaN field hNstable)
      let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
        MulAction.compHom (IBr iotaI) rhoAI
      let _ : MulAction (MulAction.stabilizer E theta) (IBr iotaI) :=
        MulAction.compHom (IBr iotaI) rhoEI
      StabilizerRestrictedCliffordCorrespondence
        (A := Gamma) (E := E) psi theta eta)
    (gallagher :
      let _ : MulAction Gamma (IBr iotaN) :=
        ambientBrauerAction N iotaN
      let rhoAI := rightConjugationOnInertiaSubgroupHom H theta
      let _ : MulAction (MulAction.stabilizer Gamma theta) (IBr iotaI) :=
        MulAction.compHom (IBr iotaI) rhoAI
      let _ : MulAction
          (BrauerGallagherTwists (Gamma := Gamma) (k := k) (K := K)
            H N iotaN theta) (IBr iotaI) :=
        brauerGallagherTwistAction H N iotaN theta iotaI productFormula
      GallagherLinearTwist
        (A := MulAction.stabilizer Gamma theta)
        (Eta := IBr iotaI)
        (BrauerGallagherTwists (Gamma := Gamma) (k := k) (K := K)
          H N iotaN theta) theta eta)
    (hOdd : CharacteristicTwoLinearBrauerTwistGroup
      (BrauerGallagherTwists (Gamma := Gamma) (k := k) (K := K)
        H N iotaN theta))
    (quotient_exponent_two :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      forall q : EffectiveConjugationQuotient H, q ^ 2 = 1)
    (thetaSemidirectFactorization :
      let _ : MulAction Gamma (IBr iotaN) :=
        ambientBrauerAction N iotaN
      let _ : MulAction E (IBr iotaN) :=
        fieldBrauerAction N iotaN field hNstable
      let hcompat := field_ambient_semidirect_compatible
        N iotaN field hNstable
      Formalisation.SemidirectStabilizerFactors field hcompat theta) :
    let _ : MulAction Gamma (IBr iotaH) :=
      ambientBrauerAction H iotaH
    let _ : MulAction E (IBr iotaH) :=
      fieldBrauerAction H iotaH field hHstable
    ProductStabilizerFactorization (A := Gamma) (E := E) psi := by
  let _ : MulAction Gamma (IBr iotaH) :=
    ambientBrauerAction H iotaH
  let _ : MulAction E (IBr iotaH) :=
    fieldBrauerAction H iotaH field hHstable
  let _ : MulAction Gamma (IBr iotaN) :=
    ambientBrauerAction N iotaN
  let _ : MulAction E (IBr iotaN) :=
    fieldBrauerAction N iotaN field hNstable
  let twists : MulAction
      (BrauerGallagherTwists (Gamma := Gamma) (k := k) (K := K)
        H N iotaN theta) (IBr iotaI) :=
    brauerGallagherTwistAction H N iotaN theta iotaI productFormula
  apply inertiaSubgroupWithField_brauerCharacter_productStabilizerFactorization
    H N iotaH iotaN psi theta iotaI field hHstable
      (field_ambient_brauer_naturality N iotaN field hNstable)
      twists eta constituents correspondence gallagher hOdd
  · exact centralizer_fixes_brauer_constituent H N hNH iotaN theta
  · exact quotient_exponent_two
  · exact productFactorization_of_semidirectStabilizerFactors
      N iotaN field hNstable theta thetaSemidirectFactorization
  · intro h p
    exact subgroup_element_fixes_brauer_character H iotaH h p

end TwoLeviApplications

end ModularRep.PaperProofs.TypeBLemma47LeviApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
