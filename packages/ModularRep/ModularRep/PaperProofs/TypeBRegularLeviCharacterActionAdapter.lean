import ModularRep.PaperProofs.TypeBRegularLeviOrbitLemma46Relative
import ModularRep.PaperProofs.TypeBRightActionOrientation
import ModularRep.StabilizerFactorizationTransport
import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# The character-action adapter for type B regular Levi subgroups

This module connects the finite action arguments in manuscript Lemmas 4.4
and 4.5 to actual function-valued irreducible Brauer characters.

The routine direct-product theorem for irreducible Brauer characters is kept
as an exact source input.  Its interface includes its usual naturality under
coordinate automorphisms.  Starting from that interface, Lean constructs the
literal coordinate automorphism of the direct-product group and the literal
right action on the tuple of factor characters.  The manuscript-specific
input is only the lower-level equality identifying conjugation by the paired
Levi with that coordinate automorphism.  The induced character-action
equation and the Cartesian orbit conclusion are derived.

The final section treats the phrase "up to an inner automorphism" in the
component return.  An equality of group automorphisms with an explicit inner
factor implies equality of the actions on actual Brauer characters.  Hence a
factorwise stabiliser theorem for the field return transports to the actual
return action.  Neither character fixedness nor a stabiliser factorisation is
assumed for the actual return.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter

open Formalisation
open ModularRep.ManuscriptVerification.ComponentReturnFull
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport
open ModularRep.PaperProofs.EvenFieldAssumption53Relative
open ModularRep.PaperProofs.TypeBRegularLeviOrbitLemma46Relative

universe u v w x

section CoordinateAutomorphisms

variable {I : Type u} (H D : I → Type v)
variable [∀ i, Group (H i)] [∀ i, Group (D i)]

/-- The automorphism of a direct product obtained by acting independently on
every factor. -/
def coordinateMulAut (factorAut : ∀ i, D i →* MulAut (H i)) :
    (∀ i, D i) →* MulAut (∀ i, H i) where
  toFun d :=
    { toFun := fun h i ↦ factorAut i (d i) (h i)
      invFun := fun h i ↦ (factorAut i (d i))⁻¹ (h i)
      left_inv := by
        intro h
        funext i
        exact (factorAut i (d i)).symm_apply_apply (h i)
      right_inv := by
        intro h
        funext i
        exact (factorAut i (d i)).apply_symm_apply (h i)
      map_mul' := by
        intro h₁ h₂
        funext i
        exact map_mul (factorAut i (d i)) (h₁ i) (h₂ i) }
  map_one' := by
    ext h i
    simp
  map_mul' := by
    intro d₁ d₂
    ext h i
    simp

@[simp]
theorem coordinateMulAut_apply
    (factorAut : ∀ i, D i →* MulAut (H i))
    (d : ∀ i, D i) (h : ∀ i, H i) (i : I) :
    coordinateMulAut H D factorAut d h i = factorAut i (d i) (h i) :=
  rfl

end CoordinateAutomorphisms

section DirectProductCharacters

variable {p : ℕ} {I : Type u} {k : Type v} {K : Type w}
variable (H D : I → Type x)
variable [Fintype I]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)] [∀ i, Group (D i)]

/-- The exact direct-product character input.

Navarro's Theorem (8.21) identifies the irreducible Brauer characters of a
finite direct product with tuples of factor characters, using the external
product formula.  The displayed naturality is the immediate coordinatewise
consequence of that formula.  This structure is an E1 source interface and
does not receive manuscript-specific proof credit. -/
structure DirectProductIBrIdentification
    (iotaProduct : PrimeRegularRootEmbedding p k K (∀ i, H i))
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i)) where
  characters : IBr iotaProduct ≃ (∀ i, IBr (iotaFactor i))
  coordinate_naturality : ∀ (d : ∀ i, D i) (psi : IBr iotaProduct),
    characters
        (IrreducibleBrauerCharacter.twist iotaProduct psi
          (coordinateMulAut H D factorAut d)) =
      fun i ↦ IrreducibleBrauerCharacter.twist (iotaFactor i)
        (characters psi i) (factorAut i (d i))

/-- The actual right action of the product of the factor automorphism groups
on the tuple of function-valued factor Brauer characters. -/
@[instance_reducible] def coordinateIBrRightAction
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i)) :
    MulAction (∀ i, D i) (∀ i, IBr (iotaFactor i)) where
  smul d psi := fun i ↦
    IrreducibleBrauerCharacter.twist (iotaFactor i) (psi i)
      (factorAut i (d i)⁻¹)
  one_smul psi := by
    funext i
    change IrreducibleBrauerCharacter.twist (iotaFactor i) (psi i)
      (factorAut i ((1 : ∀ i, D i) i)⁻¹) = psi i
    simp only [Pi.one_apply, inv_one, map_one]
    exact IrreducibleBrauerCharacter.twist_refl (iotaFactor i) (psi i)
  mul_smul d₁ d₂ psi := by
    funext i
    change IrreducibleBrauerCharacter.twist (iotaFactor i) (psi i)
        (factorAut i (((d₁ * d₂) i)⁻¹)) =
      IrreducibleBrauerCharacter.twist (iotaFactor i)
        (IrreducibleBrauerCharacter.twist (iotaFactor i) (psi i)
          (factorAut i ((d₂ i)⁻¹))) (factorAut i ((d₁ i)⁻¹))
    simp only [Pi.mul_apply, mul_inv_rev, map_mul]
    exact (IrreducibleBrauerCharacter.twist_mul (iotaFactor i) (psi i)
      (factorAut i ((d₂ i)⁻¹)) (factorAut i ((d₁ i)⁻¹))).symm

omit [Fintype I] in
@[simp]
theorem coordinateIBrRightAction_apply
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i))
    (d : ∀ i, D i) (psi : ∀ i, IBr (iotaFactor i)) (i : I) :
    let _ : MulAction (∀ i, D i) (∀ i, IBr (iotaFactor i)) :=
      coordinateIBrRightAction H D iotaFactor factorAut
    (d • psi) i = IrreducibleBrauerCharacter.twist (iotaFactor i)
      (psi i) (factorAut i (d i)⁻¹) := by
  rfl

variable {M : Type u} [Group M]

/-- Transport the actual automorphism action on the direct-product Brauer
characters to the tuple supplied by the direct-product theorem. -/
@[instance_reducible] def pairedLeviTupleAction
    (iotaProduct : PrimeRegularRootEmbedding p k K (∀ i, H i))
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i))
    (identification : DirectProductIBrIdentification H D iotaProduct
      iotaFactor factorAut)
    (sourceAut : M →* MulAut (∀ i, H i)) :
    MulAction M (∀ i, IBr (iotaFactor i)) := by
  let _ : MulAction M (IBr iotaProduct) :=
    rightAutomorphismAction iotaProduct sourceAut
  exact identification.characters.symm.mulAction M

/-- The manuscript's character-action equation follows from the lower-level
equality of group automorphisms and direct-product naturality.

In the application, `M` is the paired Levi, `rho` is its map to `Delta`, and
`source_coordinate` is the concrete conjugation identity still to be
instantiated from the regular-embedding construction. -/
theorem pairedLeviTupleAction_eq_coordinateAction
    (iotaProduct : PrimeRegularRootEmbedding p k K (∀ i, H i))
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i))
    (identification : DirectProductIBrIdentification H D iotaProduct
      iotaFactor factorAut)
    (sourceAut : M →* MulAut (∀ i, H i))
    (rho : M →* (∀ i, D i))
    (source_coordinate : ∀ m : M,
      sourceAut m = coordinateMulAut H D factorAut (rho m))
    (m : M) (psi : ∀ i, IBr (iotaFactor i)) :
    let _ : MulAction M (∀ i, IBr (iotaFactor i)) :=
      pairedLeviTupleAction H D iotaProduct iotaFactor factorAut
        identification sourceAut
    let _ : MulAction (∀ i, D i) (∀ i, IBr (iotaFactor i)) :=
      coordinateIBrRightAction H D iotaFactor factorAut
    m • psi = rho m • psi := by
  dsimp only
  let _ : MulAction M (IBr iotaProduct) :=
    rightAutomorphismAction iotaProduct sourceAut
  change identification.characters
      (IrreducibleBrauerCharacter.twist iotaProduct
        (identification.characters.symm psi) (sourceAut m⁻¹)) = _
  rw [source_coordinate m⁻¹, map_inv]
  change identification.characters
      (IrreducibleBrauerCharacter.twist iotaProduct
        (identification.characters.symm psi)
          (coordinateMulAut H D factorAut (rho m)⁻¹)) =
    fun i ↦ IrreducibleBrauerCharacter.twist (iotaFactor i) (psi i)
      (factorAut i ((rho m i)⁻¹))
  simpa using identification.coordinate_naturality (rho m)⁻¹
    (identification.characters.symm psi)

/-- The Cartesian orbit conclusion of Lemma 4.5 on the actual tuple of
factor Brauer characters.  Surjectivity of `rho` is supplied by the earlier
coinvariant-coordinate theorem, not assumed as the orbit conclusion. -/
theorem pairedLeviIBrOrbit_eq_coordinateOrbits
    (iotaProduct : PrimeRegularRootEmbedding p k K (∀ i, H i))
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i))
    (identification : DirectProductIBrIdentification H D iotaProduct
      iotaFactor factorAut)
    (sourceAut : M →* MulAut (∀ i, H i))
    (rho : M →* (∀ i, D i))
    (rho_surjective : Function.Surjective rho)
    (source_coordinate : ∀ m : M,
      sourceAut m = coordinateMulAut H D factorAut (rho m))
    (psi : ∀ i, IBr (iotaFactor i)) :
    let _ : MulAction M (∀ i, IBr (iotaFactor i)) :=
      pairedLeviTupleAction H D iotaProduct iotaFactor factorAut
        identification sourceAut
    let _ : MulAction (∀ i, D i) (∀ i, IBr (iotaFactor i)) :=
      coordinateIBrRightAction H D iotaFactor factorAut
    MulAction.orbit M psi =
      {theta | ∀ i, theta i ∈
        @MulAction.orbit (D i) (IBr (iotaFactor i))
          (rightAutomorphismAction (iotaFactor i) (factorAut i)).toSMul
          (psi i)} := by
  dsimp only
  let _ : MulAction M (∀ i, IBr (iotaFactor i)) :=
    pairedLeviTupleAction H D iotaProduct iotaFactor factorAut
      identification sourceAut
  let _ : MulAction (∀ i, D i) (∀ i, IBr (iotaFactor i)) :=
    coordinateIBrRightAction H D iotaFactor factorAut
  letI factorAction (i : I) : MulAction (D i) (IBr (iotaFactor i)) :=
    rightAutomorphismAction (iotaFactor i) (factorAut i)
  ext theta
  constructor
  · rintro ⟨m, rfl⟩ i
    have hcoordinate := pairedLeviTupleAction_eq_coordinateAction H D
      iotaProduct iotaFactor factorAut identification sourceAut rho
      source_coordinate m psi
    refine MulAction.mem_orbit_iff.mpr ⟨rho m i, ?_⟩
    exact (congrFun hcoordinate i).symm
  · intro htheta
    have hchoice : ∀ i, ∃ d : D i,
        let _ : MulAction (D i) (IBr (iotaFactor i)) :=
          rightAutomorphismAction (iotaFactor i) (factorAut i)
        d • psi i = theta i := fun i ↦
      MulAction.mem_orbit_iff.mp (htheta i)
    choose d hd using hchoice
    obtain ⟨m, hm⟩ := rho_surjective d
    refine MulAction.mem_orbit_iff.mpr ⟨m, ?_⟩
    have hcoordinate := pairedLeviTupleAction_eq_coordinateAction H D
      iotaProduct iotaFactor factorAut identification sourceAut rho
      source_coordinate m psi
    rw [hcoordinate, hm]
    funext i
    exact hd i

/-- Actual Brauer-character orbit factorisation from the source-shaped
Geck--Malle coinvariant data.

The routine direct-product character identification and its naturality are
the E1 input `identification`.  The remaining manuscript-specific action
input is the equality `source_coordinate` at the level of group
automorphisms.  Lean derives both surjectivity of the action map and the
Cartesian orbit formula; neither a character-action equation nor the orbit
formula is assumed. -/
theorem pairedLeviIBrOrbit_eq_coordinateOrbits_of_coinvariant_coordinates
    (iotaProduct : PrimeRegularRootEmbedding p k K (∀ i, H i))
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i))
    (identification : DirectProductIBrIdentification H D iotaProduct
      iotaFactor factorAut)
    (sourceAut : M →* MulAut (∀ i, H i))
    (C : I → Type x) [∀ i, Group (C i)]
    (N : ∀ i, Subgroup (D i)) [∀ i, (N i).Normal]
    (rho : M →* (∀ i, D i))
    (cocycle : M →* (∀ i, C i))
    (cocycle_surjective : Function.Surjective cocycle)
    (outerAction : ∀ i, C i →* D i ⧸ N i)
    (outerAction_surjective : ∀ i, Function.Surjective (outerAction i))
    (action_cocycle_compatible : ∀ (m : M) (i : I),
      QuotientGroup.mk' (N i) (rho m i) = outerAction i (cocycle m i))
    (rationalFactorLift : (∀ i, N i) →* M)
    (rationalFactor_action : ∀ (n : ∀ i, N i) (i : I),
      rho (rationalFactorLift n) i = n i)
    (source_coordinate : ∀ m : M,
      sourceAut m = coordinateMulAut H D factorAut (rho m))
    (psi : ∀ i, IBr (iotaFactor i)) :
    let _ : MulAction M (∀ i, IBr (iotaFactor i)) :=
      pairedLeviTupleAction H D iotaProduct iotaFactor factorAut
        identification sourceAut
    let _ : MulAction (∀ i, D i) (∀ i, IBr (iotaFactor i)) :=
      coordinateIBrRightAction H D iotaFactor factorAut
    MulAction.orbit M psi =
      {theta | ∀ i, theta i ∈
        @MulAction.orbit (D i) (IBr (iotaFactor i))
          (rightAutomorphismAction (iotaFactor i) (factorAut i)).toSMul
          (psi i)} := by
  apply pairedLeviIBrOrbit_eq_coordinateOrbits H D iotaProduct iotaFactor
    factorAut identification sourceAut rho
  · exact productActionHom_surjective_of_coinvariant_coordinates D C N rho
      cocycle cocycle_surjective outerAction outerAction_surjective
      action_cocycle_compatible rationalFactorLift rationalFactor_action
  · exact source_coordinate

end DirectProductCharacters

section InnerReturn

variable {p : ℕ} {k : Type u} {K : Type v}
variable {H : Type x} {D R : Type w}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group D] [Group R]

/-- Brauer characters cannot distinguish an automorphism from its product
with an inner automorphism on the left. -/
theorem brauerTwist_eq_of_eq_inner_mul
    (iota : PrimeRegularRootEmbedding p k K H)
    (psi : IBr iota) (actual field : MulAut H) (h : H)
    (actual_eq : actual = MulAut.conj h * field) :
    IrreducibleBrauerCharacter.twist iota psi actual =
      IrreducibleBrauerCharacter.twist iota psi field := by
  rw [actual_eq, ← IrreducibleBrauerCharacter.twist_mul]
  have hinner :
      IrreducibleBrauerCharacter.twist iota psi (MulAut.conj h) = psi := by
    apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    exact PrimeRegularClassFunction.twist_conj psi.1 h
  rw [hinner]

/-- Pointwise inner difference of two outer automorphism homomorphisms gives
identical right actions on actual irreducible Brauer characters. -/
theorem rightAutomorphismActions_eq_of_inner_difference
    (iota : PrimeRegularRootEmbedding p k K H)
    (actual field : R →* MulAut H)
    (innerDifference : ∀ r : R, ∃ h : H,
      actual r = MulAut.conj h * field r)
    (r : R) (psi : IBr iota) :
    let _ : MulAction R (IBr iota) :=
      rightAutomorphismAction iota actual
    let actualImage := r • psi
    let _ : MulAction R (IBr iota) :=
      rightAutomorphismAction iota field
    actualImage = r • psi := by
  dsimp only
  obtain ⟨h, hh⟩ := innerDifference r⁻¹
  exact brauerTwist_eq_of_eq_inner_mul iota psi (actual r⁻¹)
    (field r⁻¹) h hh

omit [Finite H] in
/-- For homomorphisms out of a cyclic group, it is enough to identify the
chosen generator up to an inner automorphism.  The same relation then holds
for every element of the cyclic group.

This is a finite group calculation.  It reduces the component-return source
obligation from a pointwise assertion on the return group to the single
group-level formula for its chosen generator. -/
theorem innerDifference_of_cyclic_generator
    (actual field : R →* MulAut H) (generator : R)
    (generator_top : Subgroup.zpowers generator = ⊤)
    (generator_difference : ∃ h : H,
      actual generator = MulAut.conj h * field generator) :
    ∀ r : R, ∃ h : H, actual r = MulAut.conj h * field r := by
  let related : Subgroup R :=
    { carrier := {r | ∃ h : H, actual r = MulAut.conj h * field r}
      one_mem' := by
        refine ⟨1, ?_⟩
        ext x
        simp
      mul_mem' := by
        rintro r s ⟨h, hr⟩ ⟨j, hs⟩
        refine ⟨h * field r j, ?_⟩
        rw [map_mul, hr, hs]
        ext x
        simp
      inv_mem' := by
        rintro r ⟨h, hr⟩
        refine ⟨(field r)⁻¹ h⁻¹, ?_⟩
        rw [map_inv, hr]
        ext x
        simp }
  have hgenerator : generator ∈ related := generator_difference
  have htop : related = ⊤ := by
    apply top_unique
    rw [← generator_top]
    exact Subgroup.zpowers_le.mpr hgenerator
  intro r
  have hr : r ∈ related := by
    rw [htop]
    exact Subgroup.mem_top r
  exact hr

/-- Group-level compatibility which makes the two right automorphism actions
of `D` and `R` into the action of a semidirect product. -/
def AutomorphismSemidirectCompatible
    (diagonal : D →* MulAut H) (outer : R →* MulAut H)
    (phi : R →* MulAut D) : Prop :=
  ∀ (r : R) (d : D),
    diagonal (phi r d) = outer r * diagonal d * (outer r)⁻¹

/-- The group-automorphism compatibility equation implies compatibility of
the actual right actions on function-valued Brauer characters. -/
theorem brauerRightActions_semidirectCompatible
    (iota : PrimeRegularRootEmbedding p k K H)
    (diagonal : D →* MulAut H) (outer : R →* MulAut H)
    (phi : R →* MulAut D)
    (compatible : AutomorphismSemidirectCompatible diagonal outer phi) :
    let _ : MulAction D (IBr iota) :=
      rightAutomorphismAction iota diagonal
    let _ : MulAction R (IBr iota) :=
      rightAutomorphismAction iota outer
    SemidirectActionCompatible (X := IBr iota) phi := by
  dsimp only
  intro r d psi
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (diagonal d⁻¹))
        (outer r⁻¹) =
    IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (outer r⁻¹))
        (diagonal ((phi r) d)⁻¹)
  rw [IrreducibleBrauerCharacter.twist_mul,
    IrreducibleBrauerCharacter.twist_mul]
  congr 1
  have hinv : diagonal ((phi r) d)⁻¹ =
      outer r * diagonal d⁻¹ * (outer r)⁻¹ := by
    calc
      diagonal ((phi r) d)⁻¹ = (diagonal ((phi r) d))⁻¹ := by
        rw [map_inv]
      _ =
          (outer r * diagonal d * (outer r)⁻¹)⁻¹ :=
        congrArg Inv.inv (compatible r d)
      _ = outer r * diagonal d⁻¹ * (outer r)⁻¹ := by
        simp [mul_assoc]
  rw [hinv]
  simp [mul_assoc]

/-- A factorwise selector theorem for a pure field return also applies to
the actual return when their automorphism homomorphisms differ pointwise by
inner automorphisms.

The conclusion is the local input required by `ComponentReturnFull`.  It is
derived from the selector factorisation for `field`, not assumed for
`actual`. -/
theorem localFactorisation_of_inner_related_return
    (iota : PrimeRegularRootEmbedding p k K H)
    (diagonal : D →* MulAut H)
    (actual field : R →* MulAut H)
    (phiActual phiField : R →* MulAut D)
    (actualCompatible :
      AutomorphismSemidirectCompatible diagonal actual phiActual)
    (fieldCompatible :
      AutomorphismSemidirectCompatible diagonal field phiField)
    (innerDifference : ∀ r : R, ∃ h : H,
      actual r = MulAut.conj h * field r)
    (psi : IBr iota)
    (fieldFactorisation :
      let _ : MulAction D (IBr iota) :=
        rightAutomorphismAction iota diagonal
      let _ : MulAction R (IBr iota) :=
        rightAutomorphismAction iota field
      let hcompat : SemidirectActionCompatible (X := IBr iota) phiField :=
        brauerRightActions_semidirectCompatible iota diagonal field phiField
          fieldCompatible
      SemidirectStabilizerFactors phiField hcompat psi) :
    let _ : MulAction D (IBr iota) :=
      rightAutomorphismAction iota diagonal
    let _ : MulAction R (IBr iota) :=
      rightAutomorphismAction iota actual
    let hcompat : SemidirectActionCompatible (X := IBr iota) phiActual :=
      brauerRightActions_semidirectCompatible iota diagonal actual phiActual
        actualCompatible
    SemidirectStabilizerFactors phiActual hcompat psi := by
  dsimp only
  letI : MulAction D (IBr iota) :=
    rightAutomorphismAction iota diagonal
  letI : MulAction R (IBr iota) :=
    rightAutomorphismAction iota actual
  have actualCompat : SemidirectActionCompatible (X := IBr iota) phiActual := by
    simpa only using
      (brauerRightActions_semidirectCompatible iota diagonal actual phiActual
        actualCompatible)
  rw [semidirectStabilizerFactors_iff_productStabilizerFactorization
    phiActual actualCompat psi]
  intro d r
  have haction :
      IrreducibleBrauerCharacter.twist iota psi (actual r⁻¹) =
        IrreducibleBrauerCharacter.twist iota psi (field r⁻¹) := by
    obtain ⟨h, hh⟩ := innerDifference r⁻¹
    exact brauerTwist_eq_of_eq_inner_mul iota psi (actual r⁻¹)
      (field r⁻¹) h hh
  have hfield : ∀ d : D, ∀ r : R,
      IrreducibleBrauerCharacter.twist iota
          (IrreducibleBrauerCharacter.twist iota psi (field r⁻¹))
            (diagonal d⁻¹) = psi ↔
        IrreducibleBrauerCharacter.twist iota psi (diagonal d⁻¹) = psi ∧
          IrreducibleBrauerCharacter.twist iota psi (field r⁻¹) = psi := by
    let fieldAction : MulAction R (IBr iota) :=
      rightAutomorphismAction iota field
    let fieldCompat : SemidirectActionCompatible (X := IBr iota) phiField := by
      simpa only using
        (brauerRightActions_semidirectCompatible iota diagonal field phiField
          fieldCompatible)
    let _ : MulAction R (IBr iota) := fieldAction
    have hf :=
      (semidirectStabilizerFactors_iff_productStabilizerFactorization
        phiField fieldCompat psi).mp fieldFactorisation
    intro d r
    exact hf d r
  change IrreducibleBrauerCharacter.twist iota
      (IrreducibleBrauerCharacter.twist iota psi (actual r⁻¹))
        (diagonal d⁻¹) = psi ↔
    IrreducibleBrauerCharacter.twist iota psi (diagonal d⁻¹) = psi ∧
      IrreducibleBrauerCharacter.twist iota psi (actual r⁻¹) = psi
  rw [haction]
  exact hfield d r

/-- Source-shaped cyclic specialization of
`localFactorisation_of_inner_related_return`: only the inner-difference
formula for the chosen return generator is required. -/
theorem localFactorisation_of_generator_inner_related_return
    (iota : PrimeRegularRootEmbedding p k K H)
    (diagonal : D →* MulAut H)
    (actual field : R →* MulAut H)
    (phiActual phiField : R →* MulAut D)
    (actualCompatible :
      AutomorphismSemidirectCompatible diagonal actual phiActual)
    (fieldCompatible :
      AutomorphismSemidirectCompatible diagonal field phiField)
    (generator : R) (generator_top : Subgroup.zpowers generator = ⊤)
    (generator_difference : ∃ h : H,
      actual generator = MulAut.conj h * field generator)
    (psi : IBr iota)
    (fieldFactorisation :
      let _ : MulAction D (IBr iota) :=
        rightAutomorphismAction iota diagonal
      let _ : MulAction R (IBr iota) :=
        rightAutomorphismAction iota field
      let hcompat : SemidirectActionCompatible (X := IBr iota) phiField :=
        brauerRightActions_semidirectCompatible iota diagonal field phiField
          fieldCompatible
      SemidirectStabilizerFactors phiField hcompat psi) :
    let _ : MulAction D (IBr iota) :=
      rightAutomorphismAction iota diagonal
    let _ : MulAction R (IBr iota) :=
      rightAutomorphismAction iota actual
    let hcompat : SemidirectActionCompatible (X := IBr iota) phiActual :=
      brauerRightActions_semidirectCompatible iota diagonal actual phiActual
        actualCompatible
    SemidirectStabilizerFactors phiActual hcompat psi := by
  exact localFactorisation_of_inner_related_return iota diagonal actual field
    phiActual phiField actualCompatible fieldCompatible
    (innerDifference_of_cyclic_generator actual field generator generator_top
      generator_difference) psi fieldFactorisation

end InnerReturn

section TransportedSemidirectActions

variable {p : ℕ} {I : Type u} {k : Type v} {K : Type w}
variable (H D : I → Type x)
variable [Fintype I]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)] [∀ i, Group (D i)]
variable {M E : Type u} [Group M] [Group E]

/-- Semidirect compatibility is preserved when both actions are transported
through the same equivalence.  This is generic action infrastructure and
receives no manuscript-specific proof credit. -/
theorem semidirectActionCompatible_transport
    {P R X Y : Type*} [Group P] [Group R]
    [MulAction P Y] [MulAction R Y]
    (phi : R →* MulAut P)
    (compatible : SemidirectActionCompatible (X := Y) phi)
    (equivalence : X ≃ Y) :
    let _ : MulAction P X := equivalence.mulAction P
    let _ : MulAction R X := equivalence.mulAction R
    SemidirectActionCompatible (X := X) phi := by
  dsimp only
  intro r p x
  apply equivalence.injective
  simpa only [Equiv.smul_def, Equiv.apply_symm_apply] using
    compatible r p (equivalence x)

/-- A group-level normalisation identity gives the semidirect compatibility
of the actual paired-Levi and field actions on the tuple of Brauer
characters.

The character action is not an input: it is transported from the literal
automorphism action on `IBr` of the direct-product group. -/
theorem pairedLeviFieldActions_semidirectCompatible
    (iotaProduct : PrimeRegularRootEmbedding p k K (∀ i, H i))
    (iotaFactor : ∀ i, PrimeRegularRootEmbedding p k K (H i))
    (factorAut : ∀ i, D i →* MulAut (H i))
    (identification : DirectProductIBrIdentification H D iotaProduct
      iotaFactor factorAut)
    (sourceAut : M →* MulAut (∀ i, H i))
    (fieldAut : E →* MulAut (∀ i, H i))
    (phiM : E →* MulAut M)
    (normalises : AutomorphismSemidirectCompatible sourceAut fieldAut phiM) :
    let _ : MulAction M (∀ i, IBr (iotaFactor i)) :=
      pairedLeviTupleAction H D iotaProduct iotaFactor factorAut
        identification sourceAut
    let _ : MulAction E (∀ i, IBr (iotaFactor i)) :=
      pairedLeviTupleAction H D iotaProduct iotaFactor factorAut
        identification fieldAut
    SemidirectActionCompatible (X := ∀ i, IBr (iotaFactor i)) phiM := by
  dsimp only
  let _ : MulAction M (IBr iotaProduct) :=
    rightAutomorphismAction iotaProduct sourceAut
  let _ : MulAction E (IBr iotaProduct) :=
    rightAutomorphismAction iotaProduct fieldAut
  have hcharacters : SemidirectActionCompatible (X := IBr iotaProduct) phiM :=
    brauerRightActions_semidirectCompatible iotaProduct sourceAut fieldAut
      phiM normalises
  exact semidirectActionCompatible_transport phiM hcharacters
    identification.characters.symm

end TransportedSemidirectActions

end ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
