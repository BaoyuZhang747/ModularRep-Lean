import ModularRep.ComponentReturnFull
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Source-shaped deductions for manuscript Lemma 4.5

This module checks the finite group and finite action deductions in the proof
of `lem:type-b-regular-levi-orbits`.  It deliberately does not reconstruct
regular embeddings, rational fixed points, or the centres of algebraic Levi
subgroups.

The strongest interface has the exact coordinate shape supplied by the
cocycle argument in the manuscript.  The Geck--Malle quotient maps onto the
product of centre coinvariants.  Their factor maps give the outer quotients
of the diagonal action images, while the direct product of rational derived
factors supplies all independent inner corrections.  Lean derives
surjectivity onto the product of the factor images, factor-supported lifts,
and then the Cartesian description of every orbit.  In particular, neither
product surjectivity nor the orbit conclusion is assumed.  The earlier
factor-supported-lift interface is retained as a lower-level theorem.  The
module also proves that the semidirect stabiliser factorisation obtained for
the effective product action pulls back to the original overgroup as soon as
the character action is identified with the action through the product image.

The second part checks the passage from the exponent-two ambient
regular-embedding quotient to the effective quotient of the paired Levi.  Its
strongest interface starts with the actual finite fixed-point inclusions,
normaliser relation, and intersection, without assuming that fixed points
commute with an algebraic central product.  Lean derives the factorisation of
squares, normality of `L C_M(L)`, and exponent two of the actual quotient.
Conclusion-shaped interfaces are retained only as lower-level lemmas.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviOrbitLemma46Relative

open ModularRep.ManuscriptVerification.ComponentReturnFull

universe u v

section ProductImageAndOrbits

variable {I M : Type u}
variable (D X : I → Type v)
variable [Group M]
variable [∀ i, Group (D i)] [∀ i, MulAction (D i) (X i)]

/-- The quotient-and-kernel data which occur in the Geck--Malle cocycle
description of a regular embedding.

`cocycle` is the regular-embedding quotient, written in coordinates indexed
by the rational factors.  The map `outer i` records the cocycle coordinate of
an automorphism in the `i`th factor image.  The direct product of the rational
factors maps back to the paired Levi through `rationalFactorLift`, and
`innerAction i` is its action on the `i`th factor.  The final field says
precisely that these rational-factor actions fill the kernel of the cocycle
coordinate.  None of the fields asserts that `rho` is onto the product of its
factor images. -/
structure CocycleCoordinateInput (C K : I → Type v)
    [∀ i, Group (C i)] [∀ i, Group (K i)]
    (rho : M →* (∀ i, D i)) where
  cocycle : M →* (∀ i, C i)
  outer : ∀ i, D i →* C i
  rationalFactorLift : (∀ i, K i) →* M
  innerAction : ∀ i, K i →* D i
  cocycle_surjective : Function.Surjective cocycle
  action_cocycle_compatible : ∀ (m : M) (i : I),
    outer i (rho m i) = cocycle m i
  rationalFactor_action : ∀ (k : ∀ i, K i) (i : I),
    rho (rationalFactorLift k) i = innerAction i (k i)
  innerAction_covers_kernel : ∀ (i : I) (d : D i), outer i d = 1 →
    ∃ k : K i, innerAction i k = d

/-- The product of the factor images follows from the cocycle quotient and
the independent rational-factor corrections.

For a prescribed tuple `d`, first lift its tuple of cocycle coordinates.
The discrepancy between `d` and that lift has trivial outer coordinate in
each factor.  The rational direct product supplies all those corrections at
once.  This is the source-shaped replacement for assuming factor-supported
lifts or product surjectivity. -/
theorem productActionHom_surjective_of_cocycle_coordinates
    (C K : I → Type v)
    [∀ i, Group (C i)] [∀ i, Group (K i)]
    (rho : M →* (∀ i, D i))
    (input : CocycleCoordinateInput D C K rho) :
    Function.Surjective rho := by
  classical
  intro d
  obtain ⟨m, hm⟩ := input.cocycle_surjective (fun i ↦ input.outer i (d i))
  let discrepancy : ∀ i, D i := fun i ↦ d i * (rho m i)⁻¹
  have discrepancy_outer : ∀ i, input.outer i (discrepancy i) = 1 := by
    intro i
    simp only [discrepancy, map_mul, map_inv]
    rw [input.action_cocycle_compatible, congrFun hm i]
    simp
  choose k hk using fun i ↦
    input.innerAction_covers_kernel i (discrepancy i) (discrepancy_outer i)
  refine ⟨input.rationalFactorLift k * m, ?_⟩
  funext i
  simp only [map_mul, Pi.mul_apply, input.rationalFactor_action, hk, discrepancy]
  simp

/-- Quotient-group specialization of the cocycle-coordinate argument.

Here `N i` is the inner-action subgroup in the `i`th factor image.  The
regular-embedding cocycle maps onto the product of the quotients by those
subgroups, while the rational derived Levi independently realizes every
tuple in their product.  Lean derives surjectivity of the actual action map;
there is no separate premise about the kernel of a quotient map. -/
theorem productActionHom_surjective_of_cocycle_quotient
    (N : ∀ i, Subgroup (D i)) [∀ i, (N i).Normal]
    (rho : M →* (∀ i, D i))
    (cocycle : M →* (∀ i, D i ⧸ N i))
    (cocycle_surjective : Function.Surjective cocycle)
    (action_cocycle_compatible : ∀ (m : M) (i : I),
      QuotientGroup.mk' (N i) (rho m i) = cocycle m i)
    (rationalFactorLift : (∀ i, N i) →* M)
    (rationalFactor_action : ∀ (k : ∀ i, N i) (i : I),
      rho (rationalFactorLift k) i = k i) :
    Function.Surjective rho := by
  let K : I → Type v := fun i ↦ N i
  let input : CocycleCoordinateInput D (fun i ↦ D i ⧸ N i) K rho :=
    { cocycle := cocycle
      outer := fun i ↦ QuotientGroup.mk' (N i)
      rationalFactorLift := rationalFactorLift
      innerAction := fun i ↦ (N i).subtype
      cocycle_surjective := cocycle_surjective
      action_cocycle_compatible := action_cocycle_compatible
      rationalFactor_action := rationalFactor_action
      innerAction_covers_kernel := by
        intro i d hd
        refine ⟨⟨d, ?_⟩, rfl⟩
        exact (QuotientGroup.eq_one_iff d).mp hd }
  exact productActionHom_surjective_of_cocycle_coordinates D
    (fun i ↦ D i ⧸ N i) K rho input

/-- The source-shaped form in which the cocycle coordinates are the actual
Geck--Malle coinvariant factors.

Each coinvariant factor maps onto the outer quotient of the corresponding
factor image.  Lean first constructs the induced quotient map to the product
of those outer quotients and proves it is surjective.  It then applies the
quotient-and-kernel correction argument above. -/
theorem productActionHom_surjective_of_coinvariant_coordinates
    (C : I → Type v) [∀ i, Group (C i)]
    (N : ∀ i, Subgroup (D i)) [∀ i, (N i).Normal]
    (rho : M →* (∀ i, D i))
    (cocycle : M →* (∀ i, C i))
    (cocycle_surjective : Function.Surjective cocycle)
    (outerAction : ∀ i, C i →* D i ⧸ N i)
    (outerAction_surjective : ∀ i, Function.Surjective (outerAction i))
    (action_cocycle_compatible : ∀ (m : M) (i : I),
      QuotientGroup.mk' (N i) (rho m i) = outerAction i (cocycle m i))
    (rationalFactorLift : (∀ i, N i) →* M)
    (rationalFactor_action : ∀ (k : ∀ i, N i) (i : I),
      rho (rationalFactorLift k) i = k i) :
    Function.Surjective rho := by
  let quotientCocycle : M →* (∀ i, D i ⧸ N i) :=
    { toFun := fun m i ↦ outerAction i (cocycle m i)
      map_one' := by
        funext i
        simp
      map_mul' := by
        intro m₁ m₂
        funext i
        simp }
  have quotientCocycle_surjective : Function.Surjective quotientCocycle := by
    intro d
    choose c hc using fun i ↦ outerAction_surjective i (d i)
    obtain ⟨m, hm⟩ := cocycle_surjective c
    refine ⟨m, ?_⟩
    funext i
    change outerAction i (cocycle m i) = d i
    rw [congrFun hm i, hc]
  exact productActionHom_surjective_of_cocycle_quotient D N rho
    quotientCocycle quotientCocycle_surjective action_cocycle_compatible
    rationalFactorLift rationalFactor_action

/-- Surjectivity onto a product constructs a lift supported on any one
factor. -/
theorem factorSupportedLift_of_surjective_action_hom
    (rho : M →* (∀ i, D i)) (rho_surjective : Function.Surjective rho) :
    ∀ (i : I) (d : D i),
      ∃ m : M, rho m i = d ∧ ∀ j, j ≠ i → rho m j = 1 := by
  classical
  intro i d
  let target : ∀ j, D j := Function.update (fun _ ↦ 1) i d
  obtain ⟨m, hm⟩ := rho_surjective target
  refine ⟨m, ?_, ?_⟩
  · simpa [target] using congrFun hm i
  · intro j hji
    simpa [target, hji] using congrFun hm j

/-- The quotient-and-kernel interface also constructs the factor-supported
lifts used by the lower-level orbit theorem. -/
theorem factorSupportedLift_of_cocycle_coordinates
    (C K : I → Type v)
    [∀ i, Group (C i)] [∀ i, Group (K i)]
    (rho : M →* (∀ i, D i))
    (input : CocycleCoordinateInput D C K rho) :
    ∀ (i : I) (d : D i),
      ∃ m : M, rho m i = d ∧ ∀ j, j ≠ i → rho m j = 1 :=
  factorSupportedLift_of_surjective_action_hom D rho
    (productActionHom_surjective_of_cocycle_coordinates D C K rho input)

/-- Factor-supported lifts derived directly from the source-shaped
coinvariant-coordinate data. -/
theorem factorSupportedLift_of_coinvariant_coordinates
    (C : I → Type v) [∀ i, Group (C i)]
    (N : ∀ i, Subgroup (D i)) [∀ i, (N i).Normal]
    (rho : M →* (∀ i, D i))
    (cocycle : M →* (∀ i, C i))
    (cocycle_surjective : Function.Surjective cocycle)
    (outerAction : ∀ i, C i →* D i ⧸ N i)
    (outerAction_surjective : ∀ i, Function.Surjective (outerAction i))
    (action_cocycle_compatible : ∀ (m : M) (i : I),
      QuotientGroup.mk' (N i) (rho m i) = outerAction i (cocycle m i))
    (rationalFactorLift : (∀ i, N i) →* M)
    (rationalFactor_action : ∀ (k : ∀ i, N i) (i : I),
      rho (rationalFactorLift k) i = k i) :
    ∀ (i : I) (d : D i),
      ∃ m : M, rho m i = d ∧ ∀ j, j ≠ i → rho m j = 1 :=
  factorSupportedLift_of_surjective_action_hom D rho
    (productActionHom_surjective_of_coinvariant_coordinates D C N rho
      cocycle cocycle_surjective outerAction outerAction_surjective
      action_cocycle_compatible rationalFactorLift rationalFactor_action)

/-- Factor-supported lifts generate the full product of the factor images.

In the application, `M` is the regular overgroup, `D i` is its image on the
`i`th rational factor, and `supportedLift` is the exact finite group content
of choosing a cocycle representative supported on one Frobenius orbit. -/
theorem productActionHom_surjective_of_supported_lifts
    [Finite I]
    (rho : M →* (∀ i, D i))
    (supportedLift : ∀ (i : I) (d : D i),
      ∃ m : M, rho m i = d ∧ ∀ j, j ≠ i → rho m j = 1) :
    Function.Surjective rho := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  intro d
  choose lift hlift using fun i : I ↦ supportedLift i (d i)
  have hliftUpdate : ∀ i,
      rho (lift i) = Function.update (fun _ ↦ 1) i (d i) := by
    intro i
    funext j
    by_cases hji : j = i
    · subst j
      simpa using (hlift i).1
    · simp [hji, (hlift i).2 j hji]
  let indices : List I := Finset.univ.toList
  refine ⟨(indices.map lift).prod, ?_⟩
  rw [map_list_prod]
  funext j
  rw [Pi.list_prod_apply]
  simp only [List.map_map]
  change (indices.map (fun i ↦ (rho (lift i)) j)).prod = d j
  simp_rw [hliftUpdate]
  have hprod := List.prod_map_eq_pow_single j
    (fun i : I ↦ Function.update (fun _ ↦ 1) i (d i) j)
    (l := indices) (by
      intro i hij hi
      simp [hij.symm])
  have hcount : indices.count j = 1 :=
    List.count_eq_one_of_mem (Finset.nodup_toList Finset.univ) (by
      simp [indices])
  rw [hcount, pow_one] at hprod
  simpa [Function.update_apply] using hprod

/-- Membership in an orbit under a product action is coordinatewise orbit
membership. -/
theorem mem_pi_orbit_iff
    (x y : ∀ i, X i) :
    y ∈ MulAction.orbit (∀ i, D i) x ↔
      ∀ i, y i ∈ MulAction.orbit (D i) (x i) := by
  constructor
  · rintro ⟨d, rfl⟩ i
    exact MulAction.mem_orbit (x i) (d i)
  · intro h
    have hchoice : ∀ i, ∃ d : D i, d • x i = y i := fun i ↦
      MulAction.mem_orbit_iff.mp (h i)
    choose d hd using hchoice
    refine MulAction.mem_orbit_iff.mpr ⟨d, ?_⟩
    funext i
    exact hd i

/-- An action which factors through a surjective product action has the same
orbit as that product action. -/
theorem orbit_eq_product_orbit_of_surjective_action_hom
    [MulAction M (∀ i, X i)]
    (rho : M →* (∀ i, D i))
    (rho_surjective : Function.Surjective rho)
    (actionCompatible : ∀ (m : M) (x : ∀ i, X i),
      m • x = rho m • x)
    (x : ∀ i, X i) :
    MulAction.orbit M x = MulAction.orbit (∀ i, D i) x := by
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨rho m, ?_⟩
    exact (actionCompatible m x).symm
  · rintro ⟨d, rfl⟩
    obtain ⟨m, rfl⟩ := rho_surjective d
    refine ⟨m, ?_⟩
    exact actionCompatible m x

/-- The source-shaped paired-Levi orbit deduction.

The hypotheses state factor-supported lifts and equality of the concrete
overgroup action with the product action.  Lean derives both the full product
image and the Cartesian product description of the orbit. -/
theorem pairedLeviOrbit_eq_coordinateOrbits
    [Finite I]
    [MulAction M (∀ i, X i)]
    (rho : M →* (∀ i, D i))
    (supportedLift : ∀ (i : I) (d : D i),
      ∃ m : M, rho m i = d ∧ ∀ j, j ≠ i → rho m j = 1)
    (actionCompatible : ∀ (m : M) (x : ∀ i, X i),
      m • x = rho m • x)
    (x : ∀ i, X i) :
    MulAction.orbit M x =
      {y | ∀ i, y i ∈ MulAction.orbit (D i) (x i)} := by
  rw [orbit_eq_product_orbit_of_surjective_action_hom D X rho
    (productActionHom_surjective_of_supported_lifts D rho supportedLift)
    actionCompatible]
  ext y
  exact mem_pi_orbit_iff D X x y

/-- The paired-Levi orbit conclusion directly from the Geck--Malle-shaped
cocycle quotient and the rational-factor kernel corrections.  Unlike
`pairedLeviOrbit_eq_coordinateOrbits`, this theorem does not take
factor-supported lifts as an input. -/
theorem pairedLeviOrbit_eq_coordinateOrbits_of_cocycle_coordinates
    (C K : I → Type v)
    [∀ i, Group (C i)] [∀ i, Group (K i)]
    [MulAction M (∀ i, X i)]
    (rho : M →* (∀ i, D i))
    (input : CocycleCoordinateInput D C K rho)
    (actionCompatible : ∀ (m : M) (x : ∀ i, X i),
      m • x = rho m • x)
    (x : ∀ i, X i) :
    MulAction.orbit M x =
      {y | ∀ i, y i ∈ MulAction.orbit (D i) (x i)} := by
  rw [orbit_eq_product_orbit_of_surjective_action_hom D X rho
    (productActionHom_surjective_of_cocycle_coordinates D C K rho input)
    actionCompatible]
  ext y
  exact mem_pi_orbit_iff D X x y

/-- Manuscript-facing quotient form of the paired-Levi orbit deduction.

The premises are the cocycle quotient, its compatibility with conjugation,
and the independent action of the rational derived factors.  The product
image and the Cartesian orbit description are both conclusions. -/
theorem pairedLeviOrbit_eq_coordinateOrbits_of_cocycle_quotient
    (N : ∀ i, Subgroup (D i)) [∀ i, (N i).Normal]
    [MulAction M (∀ i, X i)]
    (rho : M →* (∀ i, D i))
    (cocycle : M →* (∀ i, D i ⧸ N i))
    (cocycle_surjective : Function.Surjective cocycle)
    (action_cocycle_compatible : ∀ (m : M) (i : I),
      QuotientGroup.mk' (N i) (rho m i) = cocycle m i)
    (rationalFactorLift : (∀ i, N i) →* M)
    (rationalFactor_action : ∀ (k : ∀ i, N i) (i : I),
      rho (rationalFactorLift k) i = k i)
    (actionCompatible : ∀ (m : M) (x : ∀ i, X i),
      m • x = rho m • x)
    (x : ∀ i, X i) :
    MulAction.orbit M x =
      {y | ∀ i, y i ∈ MulAction.orbit (D i) (x i)} := by
  rw [orbit_eq_product_orbit_of_surjective_action_hom D X rho
    (productActionHom_surjective_of_cocycle_quotient D N rho cocycle
      cocycle_surjective action_cocycle_compatible rationalFactorLift
      rationalFactor_action)
    actionCompatible]
  ext y
  exact mem_pi_orbit_iff D X x y

/-- Paired-Levi orbit factorisation from the actual coinvariant-coordinate
form of the Geck--Malle cocycle. -/
theorem pairedLeviOrbit_eq_coordinateOrbits_of_coinvariant_coordinates
    (C : I → Type v) [∀ i, Group (C i)]
    (N : ∀ i, Subgroup (D i)) [∀ i, (N i).Normal]
    [MulAction M (∀ i, X i)]
    (rho : M →* (∀ i, D i))
    (cocycle : M →* (∀ i, C i))
    (cocycle_surjective : Function.Surjective cocycle)
    (outerAction : ∀ i, C i →* D i ⧸ N i)
    (outerAction_surjective : ∀ i, Function.Surjective (outerAction i))
    (action_cocycle_compatible : ∀ (m : M) (i : I),
      QuotientGroup.mk' (N i) (rho m i) = outerAction i (cocycle m i))
    (rationalFactorLift : (∀ i, N i) →* M)
    (rationalFactor_action : ∀ (k : ∀ i, N i) (i : I),
      rho (rationalFactorLift k) i = k i)
    (actionCompatible : ∀ (m : M) (x : ∀ i, X i),
      m • x = rho m • x)
    (x : ∀ i, X i) :
    MulAction.orbit M x =
      {y | ∀ i, y i ∈ MulAction.orbit (D i) (x i)} := by
  rw [orbit_eq_product_orbit_of_surjective_action_hom D X rho
    (productActionHom_surjective_of_coinvariant_coordinates D C N rho
      cocycle cocycle_surjective outerAction outerAction_surjective
      action_cocycle_compatible rationalFactorLift rationalFactor_action)
    actionCompatible]
  ext y
  exact mem_pi_orbit_iff D X x y

/-- The stabiliser under the original overgroup is the inverse image of the
stabiliser under its effective product action.  This is the precise lifting
step used later when the kernel of the action fixes every character. -/
theorem stabilizer_eq_comap_of_action_hom
    [MulAction M (∀ i, X i)]
    (rho : M →* (∀ i, D i))
    (actionCompatible : ∀ (m : M) (x : ∀ i, X i),
      m • x = rho m • x)
    (x : ∀ i, X i) :
    MulAction.stabilizer M x =
      (MulAction.stabilizer (∀ i, D i) x).comap rho := by
  ext m
  change m • x = x ↔ rho m • x = x
  rw [actionCompatible]

/-- Pull a semidirect-product stabiliser factorisation back from the
effective product image to the original overgroup.

In the manuscript, `M` is `L-tilde`, the product group is its image `Delta`
on `L_0`, and the kernel of `rho` fixes every Brauer character because the
action factors through `rho`.  The theorem assumes only that action
factorisation and the equality already proved for `Delta`; it derives the
corresponding equality for `M`. -/
theorem semidirectStabilizerFactors_pullback_of_action_hom
    {E : Type*} [Group E]
    [MulAction M (∀ i, X i)] [MulAction E (∀ i, X i)]
    (rho : M →* (∀ i, D i))
    (actionCompatible : ∀ (m : M) (x : ∀ i, X i),
      m • x = rho m • x)
    (phiM : E →* MulAut M)
    (phiD : E →* MulAut (∀ i, D i))
    (compatM : Formalisation.SemidirectActionCompatible
      (X := ∀ i, X i) phiM)
    (compatD : Formalisation.SemidirectActionCompatible
      (X := ∀ i, X i) phiD)
    (x : ∀ i, X i)
    (effectiveFactorisation :
      Formalisation.SemidirectStabilizerFactors phiD compatD x) :
    Formalisation.SemidirectStabilizerFactors phiM compatM x := by
  let _ := Formalisation.semidirectMulAction phiM compatM
  let _ := Formalisation.semidirectMulAction phiD compatD
  intro p
  have hEffective := effectiveFactorisation
    (⟨rho p.left, p.right⟩ : (∀ i, D i) ⋊[phiD] E)
  change
    rho p.left • (p.right • x) = x ↔
      rho p.left • x = x ∧ p.right • x = x at hEffective
  change
    p.left • (p.right • x) = x ↔
      p.left • x = x ∧ p.right • x = x
  rw [actionCompatible p.left (p.right • x), actionCompatible p.left x]
  exact hEffective

end ProductImageAndOrbits

section FieldReturn

variable {A Component : Type u} [Group A] [MulAction A Component]

/-- If the return power and a Frobenius power carry a component to the same
component, their corrected quotient fixes that component.  This is the
left-action form of the manuscript's `F^{-k} F_0^{at}` calculation. -/
theorem correctedReturn_fixes_component
    (frobenius returnElement : A) (k t : Nat) (component : Component)
    (sameTarget : returnElement ^ t • component = frobenius ^ k • component) :
    ((frobenius⁻¹) ^ k * returnElement ^ t) • component = component := by
  rw [mul_smul, sameTarget, ← mul_smul]
  simp

/-- The corrected return remains in the cyclic field group when both of its
factors do. -/
theorem correctedReturn_mem_cyclicFieldGroup
    (frobenius returnElement generator : A) (k t : Nat)
    (frobenius_mem : frobenius ∈ Subgroup.zpowers generator)
    (return_mem : returnElement ∈ Subgroup.zpowers generator) :
    (frobenius⁻¹) ^ k * returnElement ^ t ∈ Subgroup.zpowers generator := by
  exact (Subgroup.zpowers generator).mul_mem
    ((Subgroup.zpowers generator).pow_mem
      ((Subgroup.zpowers generator).inv_mem frobenius_mem) k)
    ((Subgroup.zpowers generator).pow_mem return_mem t)

end FieldReturn

section EffectiveExponent

variable {Gamma : Type u} [Group Gamma]

/-- A subgroup contained in the centre is normal.  This elementary group
theory step lets the manuscript-facing interfaces take centrality, rather
than normality, as their source input. -/
theorem centralSubgroup_normal
    (Z : Subgroup Gamma) (central : Z ≤ Subgroup.center Gamma) :
    Z.Normal := by
  constructor
  intro z hz g
  have hcomm : g * z = z * g :=
    Subgroup.mem_center_iff.mp (central hz) g
  simpa [hcomm]

/-- The copy of `L` inside `M` is normal as soon as `M` normalises `L`.

In the application, `L ≤ M` and `M ≤ N_Γ(L)` are the direct
fixed-point consequences of the definition of the paired Levi. -/
theorem Levi_comap_normal_of_le_normalizer
    (M L : Subgroup Gamma)
    (Levi_le_paired : L ≤ M)
    (paired_le_normalizer :
      M ≤ Subgroup.normalizer (L : Set Gamma)) :
    (L.comap M.subtype).Normal := by
  rw [Subgroup.comap_subtype]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer Levi_le_paired).mpr
    paired_le_normalizer

/-- The centraliser of `L` inside `M` is normal when `M` normalises `L`.
This is obtained by restricting the standard normal centraliser inside the
normaliser of `L`; centraliser normality is not an input. -/
theorem centralizer_comap_normal_of_le_normalizer
    (M L : Subgroup Gamma)
    (paired_le_normalizer :
      M ≤ Subgroup.normalizer (L : Set Gamma)) :
    ((Subgroup.centralizer (L : Set Gamma)).comap M.subtype).Normal := by
  let inclusion : M →* Subgroup.normalizer (L : Set Gamma) :=
    Subgroup.inclusion paired_le_normalizer
  let centralizerInNormalizer :
      Subgroup (Subgroup.normalizer (L : Set Gamma)) :=
    (Subgroup.centralizer (L : Set Gamma)).subgroupOf
      (Subgroup.normalizer (L : Set Gamma))
  have centralizerNormal : centralizerInNormalizer.Normal := by
    dsimp [centralizerInNormalizer]
    infer_instance
  have comapNormal : (centralizerInNormalizer.comap inclusion).Normal := by
    let _ : centralizerInNormalizer.Normal := centralizerNormal
    infer_instance
  rw [show (Subgroup.centralizer (L : Set Gamma)).comap M.subtype =
      centralizerInNormalizer.comap inclusion by
    ext x
    rfl]
  exact comapNormal

/-- The subgroup of a paired Levi corresponding to `L C_M(L)`.  It is
written inside the subtype `M`, so its second factor is exactly the
centraliser of `L` inside `M`. -/
def effectiveKernel (M L : Subgroup Gamma) : Subgroup M :=
  (L.comap M.subtype) ⊔
    ((Subgroup.centralizer (L : Set Gamma)).comap M.subtype)

/-- The literal subgroup `L C_M(L)` is normal in the paired Levi when the
paired Levi normalises `L`. -/
theorem effectiveKernel_normal_of_le_normalizer
    (M L : Subgroup Gamma)
    (Levi_le_paired : L ≤ M)
    (paired_le_normalizer :
      M ≤ Subgroup.normalizer (L : Set Gamma)) :
    (effectiveKernel M L).Normal := by
  let _ : (L.comap M.subtype).Normal :=
    Levi_comap_normal_of_le_normalizer M L Levi_le_paired
      paired_le_normalizer
  let _ : ((Subgroup.centralizer (L : Set Gamma)).comap M.subtype).Normal :=
    centralizer_comap_normal_of_le_normalizer M L paired_le_normalizer
  exact Subgroup.sup_normal _ _

/-- An exponent-two ambient quotient supplies the square factorisation used
in the paired-Levi argument.

The original group is assumed normal, as it is in a regular embedding.  Lean
derives normality of the central factor and of their product, and then lifts
the equation for squares from the quotient. -/
theorem ambientSquareFactor_of_quotient_exponent_two
    (G Z : Subgroup Gamma)
    (originalNormal : G.Normal)
    (central : Z ≤ Subgroup.center Gamma) :
    letI _ : G.Normal := originalNormal
    letI _ : Z.Normal := centralSubgroup_normal Z central
    (∀ q : Gamma ⧸ (G ⊔ Z), q ^ 2 = 1) →
      ∀ x : Gamma,
        ∃ g : Gamma, g ∈ G ∧ ∃ z : Gamma, z ∈ Z ∧ x ^ 2 = g * z := by
  let _ : G.Normal := originalNormal
  let _ : Z.Normal := centralSubgroup_normal Z central
  intro ambientExponentTwo x
  have hquotient :
      QuotientGroup.mk' (G ⊔ Z) (x ^ 2) = 1 := by
    rw [map_pow]
    exact ambientExponentTwo (QuotientGroup.mk' (G ⊔ Z) x)
  have hxSup : x ^ 2 ∈ G ⊔ Z :=
    (QuotientGroup.eq_one_iff (x ^ 2)).mp hquotient
  change x ^ 2 ∈ ((↑(G ⊔ Z) : Set Gamma)) at hxSup
  rw [Subgroup.mul_normal G Z] at hxSup
  obtain ⟨g, hg, z, hz, hgz⟩ := hxSup
  exact ⟨g, hg, z, hz, hgz.symm⟩

/-- The manuscript-specific square deduction for the effective paired-Levi
quotient.

The ambient regular-embedding quotient supplies `ambientSquareFactor`.  The
intersection input then puts its `G`-part in `L`, while centrality puts its
central part in `C_M(L)`.  Membership of the square in the effective kernel
is derived, not assumed. -/
theorem square_mem_effectiveKernel
    (G M L Z : Subgroup Gamma)
    (central_mem_pairedLevi : Z ≤ M)
    (central_centralises_Levi :
      Z ≤ Subgroup.centralizer (L : Set Gamma))
    (intersection_le_Levi : M ⊓ G ≤ L)
    (ambientSquareFactor : ∀ x : Gamma, x ∈ M →
      ∃ g : Gamma, g ∈ G ∧ ∃ z : Gamma, z ∈ Z ∧ x ^ 2 = g * z)
    (x : M) :
    x ^ 2 ∈ effectiveKernel M L := by
  obtain ⟨g, hgG, z, hzZ, hsquare⟩ :=
    ambientSquareFactor x x.property
  have hzM : z ∈ M := central_mem_pairedLevi hzZ
  have hgM : g ∈ M := by
    have hxSquare : (x : Gamma) ^ 2 ∈ M := M.pow_mem x.property 2
    have hzInv : z⁻¹ ∈ M := M.inv_mem hzM
    have hgEq : g = (x : Gamma) ^ 2 * z⁻¹ := by
      rw [hsquare]
      simp
    rw [hgEq]
    exact M.mul_mem hxSquare hzInv
  have hgL : g ∈ L := intersection_le_Levi ⟨hgM, hgG⟩
  have hzCentral : z ∈ Subgroup.centralizer (L : Set Gamma) :=
    central_centralises_Levi hzZ
  let gM : M := ⟨g, hgM⟩
  let zM : M := ⟨z, hzM⟩
  have hgKernel : gM ∈ effectiveKernel M L := by
    apply (show L.comap M.subtype ≤ effectiveKernel M L from le_sup_left)
    exact hgL
  have hzKernel : zM ∈ effectiveKernel M L := by
    apply (show (Subgroup.centralizer (L : Set Gamma)).comap M.subtype ≤
      effectiveKernel M L from le_sup_right)
    exact hzCentral
  have hxEq : x ^ 2 = gM * zM := by
    apply Subtype.ext
    exact hsquare
  rw [hxEq]
  exact (effectiveKernel M L).mul_mem hgKernel hzKernel

/-- Squares in a normal subgroup make the corresponding quotient have
exponent at most two. -/
theorem quotient_exponent_two_of_squares_mem
    {M : Type u} [Group M] (N : Subgroup M) [N.Normal]
    (squares_mem : ∀ x : M, x ^ 2 ∈ N) :
    ∀ q : M ⧸ N, q ^ 2 = 1 := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (x ^ 2)).mpr (squares_mem x)

/-- Relative form of the exponent assertion in Lemma 4.5.  The ambient
regular-embedding factorisation, the paired-Levi intersection, and the
centrality of the connected centre are explicit inputs.  Lean derives the
exponent-two conclusion for the actual effective quotient. -/
theorem pairedLevi_effectiveQuotient_exponent_two
    (G M L Z : Subgroup Gamma)
    (central_mem_pairedLevi : Z ≤ M)
    (central_centralises_Levi :
      Z ≤ Subgroup.centralizer (L : Set Gamma))
    (intersection_le_Levi : M ⊓ G ≤ L)
    (ambientSquareFactor : ∀ x : Gamma, x ∈ M →
      ∃ g : Gamma, g ∈ G ∧ ∃ z : Gamma, z ∈ Z ∧ x ^ 2 = g * z)
    (kernel_normal : (effectiveKernel M L).Normal) :
    ∀ q : M ⧸ effectiveKernel M L, q ^ 2 = 1 := by
  letI : (effectiveKernel M L).Normal := kernel_normal
  apply quotient_exponent_two_of_squares_mem (effectiveKernel M L)
  exact square_mem_effectiveKernel G M L Z central_mem_pairedLevi
    central_centralises_Levi intersection_le_Levi ambientSquareFactor

/-- Source-shaped endpoint for the exponent assertion in Lemma 4.5.

The finite fixed-point inputs are exactly those supplied by the regular-Levi
construction: `L ≤ M`, `M ≤ N_Γ(L)`, the central fixed points lie in `M`,
and `M ∩ G ≤ L`.  Unlike a finite central-product equality, these assertions
do not require fixed points to commute with an algebraic product.  Lean
derives the square factorisation and normality of the literal kernel
`L C_M(L)` before proving exponent two for the effective quotient. -/
theorem pairedLevi_effectiveQuotient_exponent_two_of_regular_embedding_data
    (G M L Z : Subgroup Gamma)
    (Levi_le_paired : L ≤ M)
    (paired_le_normalizer :
      M ≤ Subgroup.normalizer (L : Set Gamma))
    (central : Z ≤ Subgroup.center Gamma)
    (central_mem_pairedLevi : Z ≤ M)
    (intersection_le_Levi : M ⊓ G ≤ L)
    (originalNormal : G.Normal) :
    letI _ : G.Normal := originalNormal
    letI _ : Z.Normal := centralSubgroup_normal Z central
    letI _ : (effectiveKernel M L).Normal :=
      effectiveKernel_normal_of_le_normalizer M L Levi_le_paired
        paired_le_normalizer
    (∀ q : Gamma ⧸ (G ⊔ Z), q ^ 2 = 1) →
      ∀ q : M ⧸ effectiveKernel M L, q ^ 2 = 1 := by
  let _ : G.Normal := originalNormal
  let _ : Z.Normal := centralSubgroup_normal Z central
  have kernelNormal : (effectiveKernel M L).Normal :=
    effectiveKernel_normal_of_le_normalizer M L Levi_le_paired
      paired_le_normalizer
  let _ : (effectiveKernel M L).Normal := kernelNormal
  intro ambientExponentTwo
  have central_centralises_Levi :
      Z ≤ Subgroup.centralizer (L : Set Gamma) :=
    central.trans (Subgroup.center_le_centralizer (L : Set Gamma))
  have squareFactorForAll : ∀ x : Gamma,
      ∃ g : Gamma, g ∈ G ∧ ∃ z : Gamma, z ∈ Z ∧ x ^ 2 = g * z :=
    ambientSquareFactor_of_quotient_exponent_two G Z originalNormal central
      ambientExponentTwo
  have ambientSquareFactor : ∀ x : Gamma, x ∈ M →
      ∃ g : Gamma, g ∈ G ∧ ∃ z : Gamma, z ∈ Z ∧ x ^ 2 = g * z :=
    fun x _ ↦ squareFactorForAll x
  exact pairedLevi_effectiveQuotient_exponent_two G M L Z
    central_mem_pairedLevi central_centralises_Levi intersection_le_Levi
    ambientSquareFactor kernelNormal

end EffectiveExponent

section EffectiveTupleActionInfrastructure

/-! The declarations in this section are generic action infrastructure.  They
do not receive manuscript-specific proof credit.  Their purpose is to ensure
that the eventual concrete paired-Levi instance exposes only the genuine
bridges: the coordinate action, its field equivariance, and the Brauer
character tuple naturality. -/

variable {M E P X : Type*}
variable [Group M] [Group E] [Group P]
variable [MulAction P X] [MulAction E X]

/-- Data saying that an action of `M` on `X` is obtained from an effective
group `P`, compatibly with an outer action of `E`.

In the paired-Levi application, `M` is `L-tilde`, `P` is the product of the
factor images, and `rho_equivariant` is the concrete field-action square that
still has to be proved. -/
structure EffectiveTupleAction
    (phiM : E →* MulAut M) (phiP : E →* MulAut P) where
  rho : M →* P
  rho_equivariant : ∀ (e : E) (m : M),
    rho (phiM e m) = phiP e (rho m)
  compatibleP : Formalisation.SemidirectActionCompatible (X := X) phiP

namespace EffectiveTupleAction

/-- The source action obtained by restriction along the effective action
homomorphism. -/
@[instance_reducible] def sourceMulAction
    {phiM : E →* MulAut M} {phiP : E →* MulAut P}
    (A : EffectiveTupleAction (X := X) phiM phiP) : MulAction M X :=
  MulAction.compHom X A.rho

/-- Field compatibility for the source action is derived from compatibility
for the effective action and equivariance of the effective quotient map. -/
theorem sourceCompatible
    {phiM : E →* MulAut M} {phiP : E →* MulAut P}
    (A : EffectiveTupleAction (X := X) phiM phiP) :
    let _ : MulAction M X := A.sourceMulAction
    Formalisation.SemidirectActionCompatible (X := X) phiM := by
  dsimp only
  let _ : MulAction M X := A.sourceMulAction
  intro e m x
  change e • (A.rho m • x) = A.rho (phiM e m) • (e • x)
  rw [A.compatibleP, A.rho_equivariant]

/-- The homomorphism between the two semidirect products induced by the
effective action map and the identity on the field group. -/
def semidirectMap
    {phiM : E →* MulAut M} {phiP : E →* MulAut P}
    (A : EffectiveTupleAction (X := X) phiM phiP) :
    M ⋊[phiM] E →* P ⋊[phiP] E :=
  SemidirectProduct.map A.rho (MonoidHom.id E) (by
    intro e
    ext m
    exact A.rho_equivariant e m)

/-- The semidirect-product homomorphism preserves the action on `X`. -/
theorem semidirectMap_smul
    {phiM : E →* MulAut M} {phiP : E →* MulAut P}
    (A : EffectiveTupleAction (X := X) phiM phiP)
    (p : M ⋊[phiM] E) (x : X) :
    let sourceCompat := A.sourceCompatible
    let _ : MulAction M X := A.sourceMulAction
    let _ : MulAction (M ⋊[phiM] E) X :=
      Formalisation.semidirectMulAction phiM sourceCompat
    let _ : MulAction (P ⋊[phiP] E) X :=
      Formalisation.semidirectMulAction phiP A.compatibleP
    A.semidirectMap p • x = p • x := by
  dsimp only
  rfl

end EffectiveTupleAction

section ActionThroughRange

variable {A Y : Type*} [Group A] [MulAction A Y]

/-- Restriction of an action along a homomorphism factors definitionally
through the range of that homomorphism. -/
theorem smul_eq_rangeRestrict_smul
    (rho : M →* A) (m : M) (y : Y) :
    let _ : MulAction M Y := MulAction.compHom Y rho
    let _ : MulAction (MonoidHom.range rho) Y :=
      MulAction.compHom Y (MonoidHom.range rho).subtype
    m • y = rho.rangeRestrict m • y := by
  rfl

/-- An element in the kernel of the effective action homomorphism fixes every
point.  In the manuscript this is the formal content of the sentence saying
that the kernel of the action on `L_0` fixes every Brauer character. -/
theorem smul_eq_self_of_mem_ker
    (rho : M →* A) (m : M) (hm : m ∈ rho.ker) (y : Y) :
    let _ : MulAction M Y := MulAction.compHom Y rho
    m • y = y := by
  let _ : MulAction M Y := MulAction.compHom Y rho
  change rho m • y = y
  rw [show rho m = 1 from hm]
  exact one_smul A y

end ActionThroughRange

end EffectiveTupleActionInfrastructure

end ModularRep.PaperProofs.TypeBRegularLeviOrbitLemma46Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
