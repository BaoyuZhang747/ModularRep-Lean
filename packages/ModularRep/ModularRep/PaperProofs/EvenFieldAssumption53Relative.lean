import ModularRep.PaperProofs.CyclicOuterLemma37Relative
import ModularRep.FiniteFieldConformal

/-!
# The first Jordan-reduction hypothesis in Proposition 3.9

Feng--Li--Zhang, *Advances in Mathematics* 408 (2022), Assumption 5.3,
p. 30, asks that every orbit of `IBr(G^F)` under the regular overgroup
contain a character `psi` such that

* its stabiliser in the product of the regular overgroup and the chosen
  automorphism group factorises as the product of the two stabilisers, and
* `psi` extends to `G^F A_psi`.

For the even-field type `C` branch of Proposition 3.9, the manuscript argues
that the regular overgroup acts by inner automorphisms.  This file checks the
manuscript-specific deductions from that observation.  It uses actual
function-valued `IBr` objects, derives conformal fixation from
`FiniteFieldConformal`, reuses the stabiliser theorem in
`CyclicOuterLemma37Relative`, and derives the extension from the precise
Navarro (8.12) principle through `global_extension_relative`.

The following data remain explicit source or semantic inputs:

* the concrete identification of `C`, `multiplier.ker`, and the field actions
  with `CSp`, `Sp`, and the manuscript automorphisms;
* compatibility of the field action on `C` with its restriction to
  `multiplier.ker`;
* the root embeddings, the canonical group isomorphism from the kernel to
  its copy in the stabiliser, and the induced equivariant transport of
  characters; and
* Navarro's cyclic Brauer-character extension theorem.

No assumption or conclusion about BAW-goodness, iBAW, Hypothesis 5.5, or
Jordan reduction occurs below.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldAssumption53Relative

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.FiniteFieldConformal

universe u

/-- Convert the manuscript's right automorphism action into a Lean left
action.  The inverse and the opposite group cancel the two order reversals. -/
def inverseOpHom {A B : Type*} [Group A] [Group B]
    (rho : A →* B) : A →* Bᵐᵒᵖ where
  toFun a := MulOpposite.op (rho a⁻¹)
  map_one' := by simp
  map_mul' a b := by simp

/-- The function-valued right action of a group of automorphisms, encoded as
a Lean left action. -/
@[instance_reducible] def rightAutomorphismAction
    {p : Nat} {D A k K : Type*}
    [Group D] [Finite D] [Group A]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K D)
    (rho : A →* MulAut D) : MulAction A (IBr iota) :=
  MulAction.compHom (IBr iota) (inverseOpHom rho)

/-- The natural right actions of `D` and `E` on `IBr(D)` are compatible with
the semidirect product defined by an action `phi : E -> Aut(D)`.  This is a
kernel-checked action identity, not a representation theoretic input. -/
theorem rightAutomorphismSemidirectCompatible
    {p : Nat} {D E k K : Type u}
    [Group D] [Finite D] [Group E]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K D)
    (phi : E →* MulAut D) :
    let _ : MulAction D (IBr iota) :=
      rightAutomorphismAction iota (MulAut.conj : D →* MulAut D)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction iota phi
    SemidirectActionCompatible (X := IBr iota) phi := by
  dsimp only
  intro e d psi
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi
        (MulAut.conj d⁻¹)) (phi e⁻¹) =
    IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi
        (phi e⁻¹)) (MulAut.conj ((phi e) d)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul,
    IrreducibleBrauerCharacter.twist_mul]
  congr 1
  ext x
  simp

/-- Reuse the character side of `CyclicOuterLemma37Relative` by taking the
second copy of the set and its bijection to be the identity. -/
def identityActionData {H E X : Type u}
    [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]
    [MulAction H X] [MulAction E X]
    (phi : E →* MulAut H)
    (hcompat : SemidirectActionCompatible (X := X) phi)
    (hleft : forall h : H, forall x : X, h • x = x) :
    CyclicOuterLemma37Relative.ActionData
      phi (Brauer := X) (Weight := X) where
  brauerCompatible := hcompat
  weightCompatible := hcompat
  omega := Equiv.refl X
  omegaE := by intros; rfl
  brauerInnerTrivial := hleft
  weightInnerTrivial := hleft

section Conformal

variable {p : Nat} {C Fq k K E : Type u}
variable [Group C] [Finite C]
variable [Field Fq] [Finite Fq] [CharP Fq 2]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group E] [Finite E] [IsCyclic E]

/-- The exact compatibility equation saying that the field action on the
conformal group restricts to the supplied field action on the multiplier
kernel.  Keeping this equation visible prevents the concrete `CSp/Sp`
identification from being hidden inside an opaque action instance. -/
def FieldRestrictionCompatible
    (multiplier : C →* Fqˣ)
    (phiC : E →* MulAut C)
    (phiD : E →* MulAut multiplier.ker) : Prop :=
  forall (e : E) (c : C),
    MulAut.conjNormal (H := multiplier.ker) c⁻¹ * phiD e⁻¹ =
      phiD e⁻¹ *
        MulAut.conjNormal (H := multiplier.ker) ((phiC e) c)⁻¹

omit [Finite Fq] [CharP Fq 2] [Finite E] [IsCyclic E] in
/-- The supplied field-restriction equation gives the compatibility required
to act on `IBr(multiplier.ker)` by `C semidirect E`. -/
theorem conformalSemidirectCompatible
    (multiplier : C →* Fqˣ)
    (iota : PrimeRegularRootEmbedding p k K multiplier.ker)
    (phiC : E →* MulAut C)
    (phiD : E →* MulAut multiplier.ker)
    (hfield : FieldRestrictionCompatible multiplier phiC phiD) :
    let _ : MulAction C (IBr iota) :=
      rightAutomorphismAction iota
        (MulAut.conjNormal (H := multiplier.ker))
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction iota phiD
    SemidirectActionCompatible (X := IBr iota) phiC := by
  dsimp only
  intro e c psi
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi
        (MulAut.conjNormal (H := multiplier.ker) c⁻¹)) (phiD e⁻¹) =
    IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi
        (phiD e⁻¹))
      (MulAut.conjNormal (H := multiplier.ker) ((phiC e) c)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul,
    IrreducibleBrauerCharacter.twist_mul, hfield e c]

/-- The characteristic-two square-root argument makes every conformal
element fix every function-valued irreducible Brauer character of the
multiplier kernel. -/
theorem conformal_fixation
    (multiplier : C →* Fqˣ) (scalar : Fqˣ → C)
    (multiplier_scalar : forall a : Fqˣ,
      multiplier (scalar a) = a ^ 2)
    (scalar_central : forall a : Fqˣ,
      scalar a ∈ Subgroup.center C)
    (iota : PrimeRegularRootEmbedding p k K multiplier.ker) :
    let _ : MulAction C (IBr iota) :=
      rightAutomorphismAction iota
        (MulAut.conjNormal (H := multiplier.ker))
    forall c : C, forall psi : IBr iota, c • psi = psi := by
  dsimp only
  intro c psi
  exact irreducibleBrauerCharacter_fixed_of_char_two multiplier scalar
      multiplier_scalar scalar_central iota psi c⁻¹

/-- The stabiliser factorisation in FLZ Assumption 5.3, relative only to the
concrete conformal and field action data.  The theorem derives fixation and
then invokes the already checked factorisation theorem from Lemma 2.10. -/
theorem conformal_stabilizer_factorization
    (multiplier : C →* Fqˣ) (scalar : Fqˣ → C)
    (multiplier_scalar : forall a : Fqˣ,
      multiplier (scalar a) = a ^ 2)
    (scalar_central : forall a : Fqˣ,
      scalar a ∈ Subgroup.center C)
    (iota : PrimeRegularRootEmbedding p k K multiplier.ker)
    (phiC : E →* MulAut C)
    (phiD : E →* MulAut multiplier.ker)
    (hfield : FieldRestrictionCompatible multiplier phiC phiD)
    (psi : IBr iota) :
    let _ : MulAction C (IBr iota) :=
      rightAutomorphismAction iota
        (MulAut.conjNormal (H := multiplier.ker))
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction iota phiD
    let hcompat : SemidirectActionCompatible (X := IBr iota) phiC :=
      conformalSemidirectCompatible multiplier iota phiC phiD hfield
    let _ : MulAction (C ⋊[phiC] E) (IBr iota) :=
      semidirectMulAction phiC hcompat
    forall g : C ⋊[phiC] E,
      g ∈ MulAction.stabilizer (C ⋊[phiC] E) psi ↔
        exists c : C, exists e : E,
          e ∈ MulAction.stabilizer E psi ∧
            g = SemidirectProduct.inl c * SemidirectProduct.inr e := by
  dsimp only
  letI : MulAction C (IBr iota) :=
    rightAutomorphismAction iota
      (MulAut.conjNormal (H := multiplier.ker))
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction iota phiD
  have hcompat : SemidirectActionCompatible (X := IBr iota) phiC :=
    conformalSemidirectCompatible multiplier iota phiC phiD hfield
  letI : MulAction (C ⋊[phiC] E) (IBr iota) :=
    semidirectMulAction phiC hcompat
  have hleft : forall c : C, forall x : IBr iota, c • x = x :=
    conformal_fixation multiplier scalar multiplier_scalar scalar_central iota
  let A := identityActionData phiC hcompat hleft
  exact CyclicOuterLemma37Relative.global_stabilizer_factorization phiC A psi

end Conformal

section Extension

variable {p : Nat} {D E k K : Type u}
variable [Group D] [Finite D] [Group E] [Finite E] [IsCyclic E]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The extension conclusion in FLZ Assumption 5.3.

The equivalence `transport` is the still-external semantic identification of
Brauer characters of `D` with characters on the canonical copy of `D`
inside its stabiliser.  `groupEquiv_canonical` says that the supplied group
isomorphism is literally the left-factor embedding, and
`characterCompatible` says pointwise that `transport psi` is the same
function-valued character as `psi` under this isomorphism.  Thus an arbitrary
or constant character map cannot discharge the interface.  Equivariance is
also stated as an equality of actual function-valued Brauer characters.
Once these identifications are supplied, Lean proves ambient fixedness and
obtains the extension from the Navarro (8.12) principle; extension is not a
premise. -/
theorem field_stabilizer_extension_relative
    (iota : PrimeRegularRootEmbedding p k K D)
    (phi : E →* MulAut D)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (psi : IBr iota) :
    let _ : MulAction D (IBr iota) :=
      rightAutomorphismAction iota (MulAut.conj : D →* MulAut D)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction iota phi
    let hcompat : SemidirectActionCompatible (X := IBr iota) phi :=
      rightAutomorphismSemidirectCompatible iota phi
    let _ : MulAction (D ⋊[phi] E) (IBr iota) :=
      semidirectMulAction phi hcompat
    forall (iotaEmbedded : PrimeRegularRootEmbedding p k K
        (embeddedHStabilizer (phi := phi) psi))
      (groupEquiv : D ≃* embeddedHStabilizer (phi := phi) psi)
      (_groupEquiv_canonical : forall d : D,
        (((groupEquiv d : embeddedHStabilizer (phi := phi) psi) :
          D ⋊[phi] E)) = SemidirectProduct.inl d)
      (transport : IBr iota ≃ IBr iotaEmbedded)
      (_characterCompatible : forall (chi : IBr iota)
          (d : PrimeRegularElement (G := D) p),
        (transport chi).1 (PrimeRegularElement.equiv groupEquiv d) = chi.1 d),
      (forall g : semidirectStabilizer (phi := phi) psi,
        IrreducibleBrauerCharacter.twist iotaEmbedded
            (transport psi) (MulAut.conjNormal g) =
          transport ((g : D ⋊[phi] E) • psi)) →
      exists W : FDRep k (embeddedHStabilizer (phi := phi) psi),
        Representation.IsIrreducible W.ρ ∧
        (transport psi).1 =
          Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
        Nonempty (Representation.Extension
          (embeddedHStabilizer (phi := phi) psi) W.ρ) := by
  dsimp only
  letI : MulAction D (IBr iota) :=
    rightAutomorphismAction iota (MulAut.conj : D →* MulAut D)
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction iota phi
  have hcompat : SemidirectActionCompatible (X := IBr iota) phi :=
    rightAutomorphismSemidirectCompatible iota phi
  letI : MulAction (D ⋊[phi] E) (IBr iota) :=
    semidirectMulAction phi hcompat
  have hleft : forall d : D, forall x : IBr iota, d • x = x := by
    intro d x
    change IrreducibleBrauerCharacter.twist iota x
      (MulAut.conj d⁻¹) = x
    apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    exact PrimeRegularClassFunction.twist_conj x.1 d⁻¹
  let A := identityActionData phi hcompat hleft
  intro iotaEmbedded groupEquiv _groupEquiv_canonical transport
    _characterCompatible htransport
  apply CyclicOuterLemma37Relative.global_extension_relative
    phi A principle psi iotaEmbedded (transport psi)
  intro g
  rw [htransport g]
  exact congrArg transport g.property

end Extension

end ModularRep.PaperProofs.EvenFieldAssumption53Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
